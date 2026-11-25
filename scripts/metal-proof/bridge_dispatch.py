"""Symbolic execution of the ARC bridge's optimized LLVM dispatch function."""
import re
from functools import lru_cache


@lru_cache(maxsize=2048)
def instruction(line):
    """Decode only the subset in the release dispatch. Reject unknown IR."""
    clean = line.split(", !", 1)[0]
    dst, sep, op = clean.partition(" = ")
    if not sep:
        dst, op = None, dst
    if " call " in op or op.startswith("call "):
        msg = re.search(r'@"objc_msgSend\$([\w:]+)"\((.*?)\)', op)
        if msg:
            args = [v.rsplit(" ", 1)[-1] for v in msg[2].split(", ")]
            return dst, "msg", (msg[1], *args[:1], *args[2:])
        fn = re.search(r"@(llvm\.[\w.]+)\(", op)
        if fn and fn[1] in {"llvm.objc.autoreleasePoolPush", "llvm.objc.autoreleasePoolPop",
                "llvm.objc.release", "llvm.objc.retain", "llvm.objc.clang.arc.noop.use",
                "llvm.lifetime.start.p0","llvm.lifetime.end.p0"}:
            return dst, "skip", ()
    patterns = [
        ("alloc", r"alloca %struct.MTLSize, align 8"),
        ("eq", r"icmp eq (?:ptr|i32|i64) (%\d+), (%\d+|null|0)"),
        ("or", r"or i1 (%\d+), (%\d+)"),
        ("branch", r"br i1 (%\d+), label %(\d+), label %(\d+)"),
        ("jump", r"br label %(\d+)"),
        ("zext", r"zext i32 (%\d+) to i64"),
        ("phi", r"phi i64 \[ 0, %(\d+) \], \[ (%\d+), %(\d+) \]"),
        ("gep", r"getelementptr inbounds nuw (ptr|i32|i8), ptr (%\d+), i64 (%\d+|\d+)"),
        ("load", r"load (ptr|i32), ptr (%\d+), align (?:8|4)"),
        ("inc", r"add nuw nsw i64 (%\d+), 1"),
        ("store", r"store i64 (%\d+), ptr (%\d+), align 8"),
        ("splat", r"store <2 x i64> splat \(i64 (\d+)\), ptr (%\d+), align 8"),
        ("ret", r"ret void"),
    ]
    for name, pattern in patterns:
        m = re.fullmatch(pattern, op)
        if m:
            return dst, name, m.groups()
    raise ValueError(f"unclassified dispatch instruction: {line}")


def program(ir):
    body = re.search(r"^define [^\n]*@slh_metal_cmd_dispatch\([^\n]+\{\n(.*?)^\}", ir, re.M | re.S)
    if not body:
        raise ValueError("optimized dispatch is absent")
    blocks = {"entry":[]}
    block = "entry"
    for raw in body[1].splitlines():
        line = raw.split(";", 1)[0].strip()
        if line.endswith(":"):
            block = line[:-1]
            blocks[block] = []
        elif line:
            blocks[block].append(instruction(line))
    return blocks


def execute(blocks, cmd, pipe, buffers, byte_count, grid, group, scratch, use_groups):
    names = ("buffers", "pointers", "lengths", "indices")
    params = [cmd,pipe,(names[0],0),len(buffers),(names[1],0),(names[2],0),(names[3],0),
              byte_count,grid,group,scratch,use_groups]
    regs = {f"%{i}":v for i,v in enumerate(params)}
    memory = {(names[0],8*i):value for i,value in enumerate(buffers)}
    for i in range(byte_count):
        for table, stride in zip(names[1:], (8,4,4)):
            memory[table,stride*i] = (table,i,"value")
    log = []
    block, previous = "entry", None

    def get(reg):
        if reg.startswith("%"):
            return regs[reg]
        return None if reg == "null" else int(reg)

    for _ in range(200):
        for dst, op, args in blocks[block]:
            if op == "skip":
                continue
            if op == "alloc":
                val = (dst,0)
            elif op == "eq":
                val = get(args[0]) == get(args[1])
            elif op == "or":
                val = get(args[0]) or get(args[1])
            elif op in ("branch", "jump"):
                previous, block = block, args[0] if op == "jump" else args[1 if get(args[0]) else 2]
                break
            elif op == "zext":
                val = get(args[0])
            elif op == "phi":
                if previous not in (args[0], args[2]):
                    raise ValueError("unknown induction predecessor")
                val = 0 if previous == args[0] else get(args[1])
            elif op == "gep":
                kind, base, idx = args
                owner, off = get(base)
                val = owner, off + {"ptr":8, "i32":4, "i8":1}[kind] * get(idx)
            elif op == "load":
                owner, off = get(args[1])
                if (args[0] == "ptr") != (owner in ("buffers", "pointers")):
                    raise ValueError("wrong array element size")
                val = memory[owner,off]
            elif op == "inc":
                val = get(args[0]) + 1
            elif op in ("store", "splat"):
                owner, off = get(args[1])
                if not owner.startswith("%") or off not in (0,8):
                    raise ValueError("unexpected size structure access")
                memory[owner,off] = get(args[0])
                if op == "splat":
                    memory[owner,off+8] = get(args[0])
                continue
            elif op == "msg":
                name, receiver, *operands = args
                obj = get(receiver)
                values = [get(x) for x in operands]
                if name in ("encoder", "state", "buffer"):
                    val = (name,obj)
                else:
                    if name in ("dispatchThreadgroups:threadsPerThreadgroup:",
                                "dispatchThreads:threadsPerThreadgroup:"):
                        values = [tuple(memory[owner,off+i] for i in (0,8,16)) for owner,off in values]
                    log.append((name,obj,*values))
                    continue
            elif op == "ret":
                return log
            else:
                raise ValueError(op)
            regs[dst] = val
        else:
            raise ValueError("unterminated block")
    raise ValueError("dispatch exceeded its bounded loop count")


def check(ir):
    blocks = program(ir)
    count = 0
    for n in range(17):
        for k in range(9):
            for groups in (False,True):
                for scratch in (0,"scratch"):
                    buffers = [("handle",i) for i in range(n)]
                    enc = ("encoder","cmd")
                    expected = [("setComputePipelineState:",enc,("state","pipe"))]
                    expected.extend(("setBuffer:offset:atIndex:",enc,("buffer",b),0,i) for i,b in enumerate(buffers))
                    expected.extend(("setBytes:length:atIndex:",enc,("pointers",i,"value"),("lengths",i,"value"),
                                     ("indices",i,"value")) for i in range(k))
                    if scratch:
                        expected.append(("setThreadgroupMemoryLength:atIndex:",enc,scratch,0))
                    method = "dispatchThreadgroups:" if groups else "dispatchThreads:"
                    expected.append((method+"threadsPerThreadgroup:",enc,("grid",1,1),("group",1,1)))
                    got = execute(blocks,"cmd","pipe",buffers,k,"grid","group",scratch,groups)
                    if got != expected:
                        raise ValueError("compiled dispatch message operands differ from the descriptor")
                    count += 1
    for cmd, pipe, grid, group in [(None,"pipe",1,1),("cmd",None,1,1),("cmd","pipe",0,1),("cmd","pipe",1,0)]:
        if execute(blocks,cmd,pipe,[],0,grid,group,0,False):
            raise ValueError("invalid command issued a message")
    return count
