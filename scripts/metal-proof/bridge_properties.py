"""Lift compiled Objective-C property bodies to symbolic ARC calls and storage events."""
import re


def method(body):
    regs = {"%0":"self","%2":".incoming"}
    trace = []
    for raw in body.strip().splitlines():
        line = raw.strip().split(", !", 1)[0]
        dst, sep, op = line.partition(" = ")
        if not sep:
            dst, op = None, dst
        if m := re.fullmatch(r"getelementptr inbounds nuw i8, ptr %0, i64 (\d+)",op):
            regs[dst] = int(m[1])
        elif m := re.fullmatch(r"load (ptr|i64|i8), ptr (%\d+), align (\d+)",op):
            width = {"ptr":8,"i64":8,"i8":1}[m[1]]
            regs[dst] = f"(.previous {regs[m[2]]} {width})"
        elif m := re.fullmatch(r"(?:zext i1|trunc nuw i8) (%\d+) to (?:i8|i1)",op):
            # setConcurrent takes i1, the stored byte is 0/1 and the getter
            # truncates that byte. Reads of arbitrary uninitialized flags are excluded.
            regs[dst] = regs[m[1]]
        elif m := re.fullmatch(r"store (ptr|i64|i8) (%\d+), ptr (%\d+), align \d+",op):
            width = {"ptr":8,"i64":8,"i8":1}[m[1]]
            trace.append(f".write {regs[m[3]]} {width} {regs[m[2]]}")
        elif m := re.fullmatch(r"tail call (?:ptr|void) @llvm.objc.(retain|release)\(ptr (%\d+)\) #\d+",op):
            trace.append(f".{m[1]} {regs[m[2]]}")
            if dst:
                regs[dst] = regs[m[2]]
        elif m := re.fullmatch(r"tail call void @llvm.objc.storeStrong\(ptr nonnull (%\d+), ptr null\) #\d+",op):
            trace.append(f".clear {regs[m[1]]}")
        elif m := re.fullmatch(r"ret (?:ptr|i64|i1) (%\d+)",op):
            trace.append(f".result {regs[m[1]]}")
        elif op != "ret void":
            raise ValueError(f"unexpected property IR: {op}")
    return trace


def certificate(ir):
    fields = {
        "Ctx": [("device",8,True),("queue",8,True),("library",8,True)],
        "Pipeline": [("state",8,True)],
        "Buffer": [("buffer",8,True),("requestedLen",8,False)],
        "Cmd": [("cmdBuf",8,True),("encoder",8,True),("concurrent",1,False)],
    }
    headers = re.findall(r'^define internal [^\n]*?@"\\01-\[SlhMetal(\w+)Obj ([\w.:]+)\]"[^\n]*\{\n(.*?)^\}',ir,re.M|re.S)
    methods = {(cls,name):method(body) for cls,name,body in headers}
    proof = ["import Metal.BridgeProperties", "open MetalBridgeProperties"]
    def array(items):
        return "[" + ",".join(items) + "]"
    for cls, props in fields.items():
        layout = []
        for name,width,strong in props:
            getter = methods.pop((cls,name))
            setter = methods.pop((cls,"set"+name[0].upper()+name[1:]+":"))
            # Infer the proposed location from the getter. Lean checks getter,
            # setter, all pairwise byte ranges, and the destructor independently.
            offset = re.fullmatch(r"\.result \(\.previous (\d+) \d+\)",getter[-1])[1]
            layout.append(f"⟨{offset},{width},{str(strong).lower()}⟩")
            proof.append(f"example : validAccess {layout[-1]} {array(getter)} {array(setter)} := by decide")
        clears = methods.pop((cls,".cxx_destruct"))
        proof.append(f"example : validClass {array(layout)} {array(clears)} := by decide")
    if methods:
        raise ValueError(f"unclassified Objective-C methods: {list(methods)}")
    return "\n".join(proof)
