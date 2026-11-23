"""Decode indexed Keccak permutations with concrete loop counters and symbolic state words."""

from dataclasses import dataclass
from pathlib import Path
import re
import runpy

HERE = Path(__file__).parent
ir = runpy.run_path(str(HERE / "dispatch.py"))
soft = runpy.run_path(str(HERE / "soft.py"))
REG = soft["REG"]


@dataclass(frozen=True)
class Pointer:
    base: str
    offset: int


@dataclass(frozen=True)
class Word:
    value: tuple


def require(test, detail):
    if not test:
        raise ValueError(detail)


def decode(text):
    code = ir["body"](text, "proof_scalar_keccak")
    blocks = ir["blocks"](code)
    entry = re.search(
        r"^define void @proof_scalar_keccak\(ptr [^\n]*align 8 [^\n]*dereferenceable\(200\) ("
        + REG
        + r")\)",
        text,
        re.M,
    )
    require(entry is not None, "invalid Keccak state argument")
    endian = re.search(r'^target datalayout = "([eE])', text, re.M)[1]
    tables = {}
    for name, n, raw, align in re.findall(
        r'^(@[\w.]+) = [^\n]*constant \[(\d+) x i8\] c"([^"]+)", align (\d+)',
        text,
        re.M,
    ):
        data = soft["llvm_string"](raw)
        require(len(data) == int(n), "incorrect table size")
        tables[name] = (data, int(align))
    lanes = [Word(("in", i)) for i in range(25)]
    regs = {entry[1]: Pointer("state", 0)}
    constants, template = [], None
    round_key = None
    previous, block = None, "start"
    visited = set()

    def operand(var):
        if var.startswith("%"):
            require(var in regs, "read of stale or undefined SSA value " + var)
            return regs[var]
        if var.startswith("@"):
            require(var in tables, "unknown table " + var)
            return Pointer(var, 0)
        return int(var)

    def integer(var):
        value = operand(var)
        require(type(value) is int, "secret-dependent index or branch")
        return value

    for _ in range(2000):
        visited.add(block)
        instructions = blocks[block]
        old = regs.copy()
        for line in instructions[:-1]:
            q, sep, rhs = line.partition(" = ")
            if not sep:
                m = re.fullmatch(
                    r"store i64 (" + REG + r"), ptr (" + REG + r"), align 8", line
                )
                require(m is not None, "unexpected instruction " + line)
                value, ptr = map(operand, m.groups())
                require(
                    isinstance(ptr, Pointer)
                    and ptr.base == "state"
                    and 0 <= ptr.offset <= 192
                    and ptr.offset % 8 == 0
                    and isinstance(value, Word),
                    "invalid state store",
                )
                lanes[ptr.offset // 8] = value
            elif m := re.fullmatch(r"phi i(?:32|64) (.+)", rhs):
                edges = re.findall(r"\[ ([^, ]+), %([\w.]+) \]", m[1])
                require(
                    ", ".join(f"[ {v}, %{b} ]" for v, b in edges) == m[1],
                    "malformed phi",
                )
                [value] = [v for v, b in edges if b == previous]
                regs[q] = old[value] if value.startswith("%") else int(value)
            elif m := re.fullmatch(
                r"getelementptr inbounds(?: nuw)? (i8|\[(\d+) x i8\]), ptr ([@%][\w.]+), i(?:32|64) ([%\w.]+)",
                rhs,
            ):
                ptr = operand(m[3])
                index = integer(m[4])
                offset = ptr.offset + int(m[2] or 1) * index
                size = 200 if ptr.base == "state" else len(tables[ptr.base][0])
                require(0 <= index and 0 <= offset <= size, "invalid inbounds GEP")
                regs[q] = Pointer(ptr.base, offset)
            elif m := re.fullmatch(
                r"load i(32|64), ptr (" + REG + r"), align (4|8)", rhs
            ):
                width, ptr, align = int(m[1]) // 8, operand(m[2]), int(m[3])
                require(
                    isinstance(ptr, Pointer) and ptr.offset % align == 0,
                    "unaligned load",
                )
                if ptr.base == "state":
                    require(
                        width == 8 and 0 <= ptr.offset <= 192 and ptr.offset % 8 == 0,
                        "invalid state load",
                    )
                    regs[q] = lanes[ptr.offset // 8]
                else:
                    data, alignment = tables[ptr.base]
                    require(
                        0 <= ptr.offset <= len(data) - width and alignment >= align,
                        "invalid table read",
                    )
                    val = int.from_bytes(
                        data[ptr.offset : ptr.offset + width],
                        "little" if endian == "e" else "big",
                    )
                    if ptr.base.startswith("@alloc_"):
                        require(
                            round_key is None
                            and width == 8
                            and ptr.offset == 8 * len(constants),
                            "invalid round constant read",
                        )
                        round_key = val
                        regs[q] = Word(("key",))
                    else:
                        regs[q] = val
            elif m := re.fullmatch(
                r"(xor|and) i64 (" + REG + r"), (" + REG + r"|-1)", rhs
            ):
                op, left, right = m[1], operand(m[2]), operand(m[3])
                require(isinstance(left, Word), "unexpected boolean operand")
                if right == -1 and op == "xor":
                    regs[q] = Word(("not", left.value))
                else:
                    require(
                        isinstance(right, Word), "unexpected second boolean operand"
                    )
                    regs[q] = Word((op, left.value, right.value))
            elif m := re.fullmatch(
                r"tail call(?: noundef)? i64 @llvm.fshl.i64\(i64 ("
                + REG
                + r"), i64 ("
                + REG
                + r"), i64 ([%\w.]+)\)",
                rhs,
            ):
                val, n = operand(m[1]), integer(m[3])
                require(
                    m[1] == m[2] and isinstance(val, Word), "non-rotation funnel shift"
                )
                regs[q] = Word(("rot", n % 64, val.value))
            elif m := re.fullmatch(
                r"add nuw(?: nsw)? i(32|64) (" + REG + r"), (\d+)", rhs
            ):
                n = integer(m[2]) + int(m[3])
                require(0 <= n < 2 ** (int(m[1]) - 1), "counter overflow")
                regs[q] = n
            elif m := re.fullmatch(r"zext i32 (" + REG + r") to i64", rhs):
                n = integer(m[1])
                require(0 <= n < 2**32, "invalid unsigned extension")
                regs[q] = n
            elif m := re.fullmatch(r"icmp eq i(?:32|64) (" + REG + r"), (\d+)", rhs):
                regs[q] = integer(m[1]) == int(m[2])
            else:
                raise ValueError("uninterpreted indexed Keccak instruction: " + line)
        tail = instructions[-1]
        if tail == "ret void":
            require(
                len(constants) == 24 and round_key is None and visited == set(blocks),
                "incomplete permutation CFG",
            )
            require(
                lanes == [Word(("in", i)) for i in range(25)],
                "return changed the final state",
            )
            return template, constants
        if m := re.fullmatch(r"br label %([\w.]+)", tail):
            target = m[1]
        else:
            m = re.fullmatch(
                r"br i1 (" + REG + r"), label %([\w.]+), label %([\w.]+)", tail
            )
            require(
                m is not None and type(operand(m[1])) is bool, "unsupported conditional"
            )
            target = m[2] if operand(m[1]) else m[3]
        if round_key is not None:
            # At the outer latch all 25 words reside in their original array.
            # Replace exact copies of these words in live registers by the new
            # inputs. Any later use of a different old symbolic word fails.
            out = tuple(x.value for x in lanes)
            if template is None:
                template = out
            require(
                template == out and len(set(out)) == 25,
                "rounds have different circuits",
            )
            constants.append(round_key)
            round_key = None
            forwarded = {word: Word(("in", i)) for i, word in enumerate(lanes)}
            regs = {
                k: forwarded[v] if isinstance(v, Word) else v
                for k, v in regs.items()
                if not isinstance(v, Word) or v in forwarded
            }
            lanes = [Word(("in", i)) for i in range(25)]
        previous, block = block, target
    raise ValueError("indexed Keccak control flow did not terminate")


def program(text):
    output, constants = decode(text)
    definitions = []
    names = {}

    def name(node):
        if node[0] == "in":
            return f"a[{node[1]}]!"
        if node[0] == "key":
            return "rc"
        if node not in names:
            if node[0] in ("xor", "and"):
                left, right = map(name, node[1:])
                expr = left + (" ^^^ " if node[0] == "xor" else " &&& ") + right
            elif node[0] == "rot":
                expr = f"({name(node[2])}).rotateLeft {node[1]}"
            elif node[0] == "not":
                expr = f"~~~({name(node[1])})"
            else:
                raise ValueError(node[0])
            names[node] = f"v{len(definitions)}"
            definitions.append(f"  let {names[node]} := {expr}\n")
        return names[node]

    rows = list(map(name, output))
    return (
        "import Spec.ShakeWords\nopen Spec.Keccak\nnamespace PeerKeccak.Indexed\n\n"
        "def round (a : State) (rc : Lane) : State :=\n"
        + "".join(definitions)
        + "  #["
        + ",".join(rows)
        + "]\n\n"
        "def constants : Array Lane := #[\n  "
        + ",\n  ".join(f"0x{k:016x}" for k in constants)
        + "]\n"
        "def permute (a : State) : State := constants.foldl round a\nend PeerKeccak.Indexed\n"
    )
