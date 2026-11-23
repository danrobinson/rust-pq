"""Copy-only LLVM trace checker for the pinned peer's signature codecs.

Each input byte has a distinct symbolic origin. Branches and addresses must
resolve without inspecting any symbolic byte. Reject any unmodeled reachable
operation. Successful heap allocation is assumed for Vec-returning codecs.
This is a checked fragment of LLVM, using little-endian byte memory on the
three explicit 64-bit targets. It is an independent byte-origin check, with
the Rust compiler and this interpreter in its trust boundary.
"""

import re
from dataclasses import dataclass

REG = r"%[-\w.$]+"
TOKEN = rf"(?:{REG}|-?\d+|null|false|true)"


@dataclass(frozen=True)
class Pointer:
    block: int
    offset: int = 0


class OtherLength:
    """A universally quantified valid slice length unequal to the required size."""

    def __init__(self, excluded):
        self.excluded = excluded

    def __eq__(self, other):
        if type(other) is int and other == self.excluded:
            return False
        raise ValueError("unsupported comparison of symbolic length")


def parts(args):
    # Function argument attributes can themselves contain comma-separated lists.
    start = depth = 0
    out = []
    for i, c in enumerate(args):
        if c in "(<[":
            depth += 1
        if c in ")>]":
            depth -= 1
        if c == "," and not depth:
            out.append(args[start:i].strip())
            start = i + 1
    if args[start:].strip():
        out.append(args[start:].strip())
    return out


def size_of(ty):
    if match := re.fullmatch(r"i(\d+)", ty):
        bits = int(match[1])
        if bits not in (1, 8, 16, 32, 64, 128):
            raise ValueError(f"unsupported scalar layout: {ty}")
        return (bits + 7) // 8
    if match := re.fullmatch(r"(?:\[(\d+) x (.*)\]|<(\d+) x (.*)>)", ty):
        n, elem = (match[1], match[2]) if match[1] else (match[3], match[4])
        size = int(n) * size_of(elem)
        if match[3] and (elem == "i1" or size == 0 or size & (size - 1)):
            raise ValueError(f"unsupported vector layout: {ty}")
        return size
    raise ValueError(f"unsupported LLVM type {ty}")


class Machine:
    def __init__(self, ir):
        self.functions = {}
        self.aliases = dict(
            re.findall(r"^@([^\s]+) = .*?alias .*?, ptr @([^\s]+)\s*$", ir, re.M)
        )
        for match in re.finditer(
            r"^define [^\n]*?@([^ (]+)\(([^\n]*)\) [^\n]*\{\n(.*?)^\}", ir, re.M | re.S
        ):
            name, params, body = match.groups()
            registers = []
            for param in parts(params):
                if end := re.search(r"(%[-\w.$]+)$", param):
                    registers.append(end[1])
                else:
                    registers.append(None)
            blocks = {}
            label = None
            for line in body.splitlines():
                line = line.split(";", 1)[0].strip()
                if not line:
                    continue
                if line.endswith(":"):
                    label = line[:-1]
                    blocks[label] = []
                else:
                    if label is None:
                        # LLVM numbers an unnamed entry block immediately after
                        # any unnamed argument registers.
                        numbers = [
                            int(x[1:]) for x in registers if x and x[1:].isdigit()
                        ]
                        label = str(max(numbers, default=-1) + 1)
                        blocks[label] = []
                    blocks[label].append(line.split(", !", 1)[0])
            self.functions[name] = (registers, blocks)
        self.blocks = []
        self.alignments = []
        self.dead = set()
        self.readonly = set()
        self.steps = 0

    def allocate(self, cells, align):
        self.blocks.append(cells)
        self.alignments.append(align)
        return Pointer(len(self.blocks) - 1)

    def region(self, p, length, align=1, write=False):
        if not isinstance(p, Pointer) or p.block in self.dead:
            raise ValueError(f"invalid memory access {p}")
        if not (0 <= p.offset <= p.offset + length <= len(self.blocks[p.block])):
            raise ValueError(f"out-of-bounds access {p} of length {length}")
        if write and p.block in self.readonly:
            raise ValueError("write to a read-only input")
        if self.alignments[p.block] < align or p.offset % align:
            raise ValueError(f"alignment {align} unavailable at {p}")
        return self.blocks[p.block], slice(p.offset, p.offset + length)

    @staticmethod
    def number(value):
        if not isinstance(value, int) or value < 0:
            raise ValueError(
                f"symbolic input used as an address, branch or arithmetic operand: {str(value)[:100]}"
            )
        return value

    @staticmethod
    def cells(value, size):
        if isinstance(value, tuple) and len(value) == size:
            return value
        if isinstance(value, int) and 0 <= value < 1 << (size * 8):
            return value.to_bytes(size, "little")
        raise ValueError("unsupported value stored")

    def execute(self, name, arguments):
        if name in self.aliases:
            return self.execute(self.aliases[name], arguments)
        if name not in self.functions:
            raise ValueError(f"unmodeled called function {name}")
        formals, blocks = self.functions[name]
        if len(formals) != len(arguments) or None in formals:
            raise ValueError(f"unexpected function signature {name}")
        registers = dict(zip(formals, arguments))
        local_objects = []
        label = next(iter(blocks))
        previous = None

        def val(token):
            if token.startswith("%"):
                if token not in registers:
                    raise ValueError(
                        f"undefined register {token} in {name}:{label} at {line[:130]}"
                    )
                return registers[token]
            if token in ("false", "true"):
                return int(token == "true")
            if token == "null":
                return None
            return int(token)

        def final_arg(arg):
            return val(re.search(rf"({TOKEN})$", arg)[1])

        while True:
            phis = {}
            for line in blocks[label]:
                self.steps += 1
                if self.steps > 20_000_000:
                    raise ValueError("trace bound exceeded")
                assignment = re.fullmatch(rf"({REG}) = (.*)", line)
                reg, ins = assignment.groups() if assignment else (None, line)
                if ins.startswith("phi "):
                    choices = dict(
                        (pred, src)
                        for src, pred in re.findall(
                            rf"\[ ({TOKEN}), %([-\w.$]+) \]", ins
                        )
                    )
                    phis[reg] = val(choices[previous])
                    continue
                if phis:
                    registers.update(phis)
                    phis.clear()
                if ins.startswith("br "):
                    if m := re.fullmatch(r"br label %([-\w.$]+)", ins):
                        dest = m[1]
                    elif m := re.fullmatch(
                        rf"br i1 ({TOKEN}), label %([-\w.$]+), label %([-\w.$]+)", ins
                    ):
                        dest = m[2] if self.number(val(m[1])) else m[3]
                    else:
                        raise ValueError(ins)
                    previous, label = label, dest
                    break
                if ins == "ret void" or ins.startswith("ret i"):
                    value = None if ins == "ret void" else final_arg(ins)
                    self.dead.update(local_objects)
                    return value
                if m := re.fullmatch(r"alloca (.*), align (\d+)", ins):
                    result = self.allocate([None] * size_of(m[1]), int(m[2]))
                    local_objects.append(result.block)
                elif m := re.fullmatch(
                    r"getelementptr (?:inbounds )?(?:nuw )?(.*?), ptr ("
                    + REG
                    + r"), (.*)",
                    ins,
                ):
                    element, base, indices = m.groups()
                    p = val(base)
                    indexes = parts(indices)
                    offset = 0
                    for j, idx in enumerate(indexes):
                        if j:
                            element = re.fullmatch(r"\[\d+ x (.*)\]", element)[1]
                        raw = final_arg(idx)
                        if not isinstance(raw, int):
                            raise ValueError("symbolic pointer offset")
                        width = int(re.match(r"i(\d+)", idx)[1])
                        idx_value = raw % (1 << width)
                        if idx_value >= 1 << (width - 1):
                            idx_value -= 1 << width
                        offset += idx_value * size_of(element)
                    result = Pointer(p.block, p.offset + offset)
                    if "inbounds" in ins:
                        self.region(result, 0)
                elif m := re.fullmatch(
                    r"load (.*?), ptr (" + REG + r"), align (\d+)", ins
                ):
                    cells, sl = self.region(val(m[2]), size_of(m[1]), int(m[3]))
                    data = tuple(cells[sl])
                    if None in data:
                        raise ValueError("read uninitialized memory")
                    result = (
                        int.from_bytes(bytes(data), "little")
                        if all(i >= 0 for i in data)
                        else data
                    )
                elif m := re.fullmatch(
                    r"store (.*?) (" + TOKEN + r"), ptr (" + REG + r"), align (\d+)",
                    ins,
                ):
                    size = size_of(m[1])
                    cells, sl = self.region(val(m[3]), size, int(m[4]), write=True)
                    cells[sl] = self.cells(val(m[2]), size)
                    continue
                elif m := re.fullmatch(
                    rf"select i1 ({TOKEN}), (?:i\d+|ptr) ({TOKEN}), (?:i\d+|ptr) ({TOKEN})",
                    ins,
                ):
                    result = val(m[2] if self.number(val(m[1])) else m[3])
                elif m := re.fullmatch(
                    r"icmp (?:samesign )?(eq|ne|ult|ule|ugt|uge) (?:i(\d+)|ptr) ("
                    + TOKEN
                    + r"), ("
                    + TOKEN
                    + r")",
                    ins,
                ):
                    a, b = val(m[3]), val(m[4])
                    if isinstance(a, tuple) or isinstance(b, tuple):
                        raise ValueError("comparison inspects symbolic data")
                    if m[2] and isinstance(a, int) and isinstance(b, int):
                        mask = (1 << int(m[2])) - 1
                        a, b = a & mask, b & mask
                    if "samesign" in ins:
                        signbit = 1 << (int(m[2]) - 1)
                        if (a & signbit) != (b & signbit):
                            raise ValueError("samesign predicate poison")
                    if m[1] in ("eq", "ne"):
                        result = (a == b) == (m[1] == "eq")
                    else:
                        mask = (1 << int(m[2])) - 1
                        a, b = self.number(a) & mask, int(b) & mask
                        result = {
                            "ult": a < b,
                            "ule": a <= b,
                            "ugt": a > b,
                            "uge": a >= b,
                        }[m[1]]
                elif m := re.fullmatch(
                    r"(add|sub|mul|and|or|xor|shl|lshr) ((?:(?:nuw|nsw|disjoint) )*)i(\d+) ("
                    + TOKEN
                    + r"), ("
                    + TOKEN
                    + r")",
                    ins,
                ):
                    op, flags, width = m[1], m[2], int(m[3])
                    limit = 1 << width
                    a, b = val(m[4]), val(m[5])
                    if not isinstance(a, int) or not isinstance(b, int):
                        raise ValueError("arithmetic on symbolic bytes")
                    a, b = a % limit, b % limit
                    if op in ("lshr", "shl") and b >= width:
                        raise ValueError("poison shift")

                    def calc(x, y):
                        if op == "add":
                            return x + y
                        if op == "sub":
                            return x - y
                        if op == "mul":
                            return x * y
                        if op == "and":
                            return x & y
                        if op == "or":
                            return x | y
                        if op == "xor":
                            return x ^ y
                        if op == "shl":
                            return x << y
                        return x >> y

                    result = calc(a, b)
                    if "nuw" in flags and not 0 <= result < limit:
                        raise ValueError("unsigned overflow")
                    signed = lambda x: x if x < limit // 2 else x - limit
                    if (
                        "nsw" in flags
                        and not -limit // 2 <= calc(signed(a), signed(b)) < limit // 2
                    ):
                        raise ValueError("signed overflow")
                    if "disjoint" in flags and a & b:
                        raise ValueError("overlapping disjoint operands")
                    result %= limit
                elif m := re.fullmatch(
                    r"(trunc|zext) ((?:(?:nuw|nneg) )*)i(\d+) ("
                    + TOKEN
                    + r") to i(\d+)",
                    ins,
                ):
                    result = self.number(val(m[4]))
                    if "nneg" in m[2] and result >= 1 << (int(m[3]) - 1):
                        raise ValueError("negative nneg extension")
                    if "nuw" in m[2] and result >= 1 << int(m[5]):
                        raise ValueError("lossy nuw truncation")
                    result %= 1 << int(m[5])
                elif m := re.fullmatch(
                    r"(?:tail )?call .*?@([^ (]+)\((.*)\)(?: #[0-9]+)?", ins
                ):
                    callee, args = m[1], parts(m[2])
                    if callee.startswith("llvm.lifetime."):
                        p = final_arg(args[0])
                        if p.block not in local_objects or p.offset:
                            raise ValueError("nonlocal lifetime marker")
                        if ".end." in callee:
                            self.dead.add(p.block)
                        else:
                            self.dead.discard(p.block)
                            self.blocks[p.block][:] = [None] * len(self.blocks[p.block])
                        continue
                    if callee == "llvm.experimental.noalias.scope.decl":
                        continue
                    av = [final_arg(a) for a in args]
                    if callee.startswith("llvm.memcpy."):
                        dst, src, n, volatile = av
                        if volatile:
                            raise ValueError("volatile copy")
                        n = self.number(n)

                        def arg_align(arg):
                            align = re.search(r"\balign (\d+)\b", arg)
                            return int(align[1]) if align else 1

                        sc, ss = self.region(src, n, arg_align(args[1]))
                        dc, ds = self.region(dst, n, arg_align(args[0]), write=True)
                        if sc is dc and max(ss.start, ds.start) < min(ss.stop, ds.stop):
                            raise ValueError("overlapping memcpy")
                        dc[ds] = sc[ss]
                        continue
                    if callee.startswith("llvm.memset."):
                        dst, byte, n, vol = av
                        if vol:
                            raise ValueError("volatile memset")
                        dc, ds = self.region(dst, self.number(n), write=True)
                        dc[ds] = [self.number(byte)] * n
                        continue
                    if callee.startswith("llvm.umax."):
                        result = max(map(self.number, av))
                    elif callee.startswith("llvm.usub.sat."):
                        result = max(0, self.number(av[0]) - self.number(av[1]))
                    elif callee.endswith("___rust_no_alloc_shim_is_unstable_v2"):
                        continue
                    elif callee in ("malloc", "calloc"):
                        args = list(map(self.number, av))
                        n = args[0] if callee == "malloc" else args[0] * args[1]
                        result = self.allocate(
                            ([None] if callee == "malloc" else [0]) * n, 16
                        )
                    elif callee == "free":
                        (ptr,) = av
                        if ptr is not None:
                            if ptr.offset or ptr.block in self.dead:
                                raise ValueError("invalid free")
                            self.dead.add(ptr.block)
                        continue
                    elif callee.endswith(("___rust_alloc", "___rust_alloc_zeroed")):
                        n, align = map(self.number, av)
                        result = self.allocate(
                            ([0] if callee.endswith("zeroed") else [None]) * n, align
                        )
                    elif callee.endswith("___rust_dealloc"):
                        p, n, align = av
                        if (
                            p.offset
                            or len(self.blocks[p.block]) != n
                            or self.alignments[p.block] != align
                            or p.block in self.dead
                        ):
                            raise ValueError("invalid deallocation")
                        self.dead.add(p.block)
                        continue
                    else:
                        result = self.execute(callee, av)
                else:
                    raise ValueError(
                        f"unsupported reached instruction in {name} at {label}: {ins[:190]}"
                    )
                if reg:
                    registers[reg] = result
            else:
                raise ValueError(f"block without terminator {name}:{label}")


def check(ir, name, size):
    machine = Machine(ir)
    independent = [-i - 1 for i in range(size)]
    source = machine.allocate(independent.copy(), 1)
    machine.readonly.add(source.block)
    output = machine.allocate([None] * size, 1)
    machine.execute(name, [source, output])
    if (
        machine.blocks[source.block] != independent
        or machine.blocks[output.block] != independent
    ):
        raise ValueError(f"incorrect serialized byte origins: {name}")
    return machine.steps


def check_invalid(ir, name, size):
    machine = Machine(ir)
    # No input bytes can be read on this path, whichever legal pointer was supplied.
    source = machine.allocate([], 1)
    if machine.execute(name, [source, OtherLength(size)]) != 0:
        raise ValueError(f"incorrect invalid-length behavior: {name}")
    return machine.steps
