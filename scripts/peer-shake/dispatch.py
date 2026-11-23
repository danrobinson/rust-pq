"""Check closed control flow, function targets and state operands of the Keccak selector."""
import re

SOFT = r"_R\w*6keccak8backends4soft8keccak_pyKj18_\w+"
ARM = r"_RN\w*6keccak8backends12aarch64_sha316p1600_armv8_sha3"
INNER = r"_R\w*12with_backend18aarch64_sha3_inner\w*21proof_dispatch_keccak\w+"


def body(text, name):
    m = re.search(r"^define [^\n]*@" + name + r"\([^\n]*\)[^\n]*\{\n(.+?)^\}", text, re.M | re.S)
    if not m:
        raise ValueError("missing Keccak symbol " + name)
    return m[1]


def blocks(code):
    result = {}
    for line in code.splitlines():
        line = line.split(";", 1)[0].strip()
        if not line or line.startswith("tail call void @llvm.experimental.noalias.scope.decl(metadata !"):
            continue
        if line.endswith(":"):
            label = line[:-1]
            if label in result:
                raise ValueError(label)
            result[label] = []
        else:
            result[label].append(re.sub(r", !.*$", "", line))
    return result


def called(line, name, *, round_arg=False):
    ptr = r"ptr noalias nofree noundef nonnull align 8 dereferenceable\(200\) %state"
    m = re.fullmatch(r"tail call (?:fastcc )?void @("+name+r")\("+ptr+(r", i64 noundef 24" if round_arg else "")+r"\)",line)
    if not m:
        raise ValueError("unexpected Keccak call " + line)
    return m[1]


def direct(code, name, *, round_arg=False):
    graph = blocks(code)
    if list(graph) != ["start"] or len(graph["start"]) != 2 or graph["start"][1] != "ret void":
        raise ValueError("expected one direct Keccak call")
    return called(graph["start"][0], name, round_arg=round_arg)


def select(text, target):
    public = body(text, "proof_dispatch_keccak")
    if target.startswith("x86_64"):
        kernel = direct(public, SOFT)
    elif target == "aarch64-apple-darwin":
        direct(public, ARM, round_arg=True)
        return text
    else:
        graph = blocks(public)
        start = graph["start"]
        if len(start) != 3 or len(graph) != 4:
            raise ValueError("invalid Arm Keccak selector")
        feature = re.fullmatch(r"(%\w+) = load atomic i8, ptr @_R\w*6keccak21armv8_sha3_intrinsics7STORAGE monotonic, align 1", start[0])
        flag = re.fullmatch(r"(%[\w.]+) = icmp eq i8 "+re.escape(feature[1])+", 1", start[1])
        jump = re.fullmatch(r"br i1 "+re.escape(flag[1])+r", label %([\w.]+), label %([\w.]+)", start[2])
        yes, no = graph[jump[1]], graph[jump[2]]
        if len(yes)!=2 or len(no)!=2 or yes[1]!=no[1]:
            raise ValueError("unexpected Arm/control join")
        join = re.fullmatch(r"br label %([\w.]+)", yes[1])
        if graph[join[1]] != ["ret void"]:
            raise ValueError("unexpected continuation")
        helper = called(yes[0], INNER)
        entry = re.search(r"^define [^\n]*@"+re.escape(helper)+r"\(ptr [^,\n]*dereferenceable\(200\) (%[\w.]+)\)", text, re.M)
        if not entry:
            raise ValueError("unexpected SHA3 thunk operand")
        direct(re.sub(re.escape(entry[1])+r"\b", "%state", body(text, helper)), ARM, round_arg=True)
        kernel = called(no[0], SOFT)
    if direct(body(text, "proof_scalar_keccak"), SOFT) != kernel:
        raise ValueError("proof entry does not select public scalar object")
    # Expose the selected kernel body under the uniform input name used by
    # the SSA decoder. For Apple the scalar entry contains the inlined body.
    source = re.escape(kernel)
    renamed, changes = re.subn(r"^define internal fastcc void @"+source+r"\(", "define void @proof_scalar_keccak(",
                               text.replace("define void @proof_scalar_keccak(", "define void @other_entry("), flags=re.M)
    if changes != 1:
        raise ValueError("expected unique scalar definition")
    return renamed
