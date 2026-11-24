"""Interpret the native rate-block word/byte mapping on each checked target."""

from pathlib import Path
import re
import runpy

HERE = Path(__file__).parent
IR = runpy.run_path(str(HERE.parent / "peer-shake/dispatch.py"))
REG = r"%[\w.]+"
LANES = r"(?:i64|<2 x i64>)"


def prepare(path, locked):
    locked["unpack"](path, "sha3", "0.11.0")
    lib = path / "src/lib.rs"
    src = lib.read_text()
    if src.count("#![forbid(unsafe_code)]") != 1:
        raise ValueError("unexpected SHA-3 attributes")
    lib.write_text(src.replace("#![forbid(unsafe_code)]", "#![deny(unsafe_code)]"))
    api = path / "src/block_api.rs"
    before, marker, body = api.read_text().partition("    fn read_block(&mut self)")
    call = "self.keccak.with_f1600("
    if not marker or body.count(call) != 1:
        raise ValueError("unexpected SHA-3 squeeze permutation call")
    api.write_text(
        before
        + marker
        + body.replace(call, "peer_select(")
        + "\n"
        + (HERE / "words.rs").read_text()
    )


def check(condition, detail):
    if not condition:
        raise ValueError(detail)


def inspect(text, bits):
    endian = re.search(r'^target datalayout = "([eE])', text, re.M)[1]
    logical = [i if endian == "e" else i // 8 * 8 + 7 - i % 8 for i in range(200)]
    initial = [("state", i) for i in logical]
    after = [("permutation", i) for i in logical]
    block = [("block", i) for i in range(136)]

    def xor(a, b):
        return tuple(sorted((a, b)))

    for op in ("absorb", "read"):
        state = "%s" if op == "absorb" else "%r"
        buf = "%b" if op == "absorb" else "%out"
        name = "proof_" + op + "_bytes"
        declaration = re.search(
            r"^define [^\n]+@" + name + r"\(([^\n]+)\) unnamed_addr", text, re.M
        )[1]
        check(
            re.findall(REG, declaration) == [state, buf]
            and "dereferenceable(200) " + state in declaration
            and "dereferenceable(136)" in declaration,
            "invalid ABI: " + name,
        )
        state_alignment = int(
            re.search(r"align (4|8) [^,]*dereferenceable\(200\)", declaration)[1]
        )
        memory = {
            state: initial.copy(),
            buf: block.copy() if op == "absorb" else [None] * 136,
        }
        alignment = {state: state_alignment, buf: 1}
        pointers = {base: (base, 0) for base in memory}
        regs = {}
        called = False

        def access(ptr, n, align):
            region, off = pointers[ptr]
            check(
                0 <= off
                and off + n <= len(memory[region])
                and off % align == 0
                and alignment[region] >= align,
                "invalid pointer " + ptr,
            )
            return region, off

        def read(ptr, n, align):
            r, o = access(ptr, n, align)
            value = memory[r][o : o + n]
            check(None not in value, "uninitialized load")
            return value

        def put(ptr, value, align):
            r, o = access(ptr, len(value), align)
            memory[r][o : o + len(value)] = value

        def pointer_arg(operand, n):
            pointer = re.search(REG + "$", operand)[0]
            align = re.search(r"align (\d+)", operand)
            extent = re.search(r"dereferenceable\((\d+)\)", operand)
            a = int(align[1]) if align else 1
            access(pointer, max(n, int(extent[1]) if extent else 0), a)
            return pointer, a

        [instructions] = IR["blocks"](IR["body"](text, name)).values()
        check(instructions[-1] == "ret void", "invalid return")
        for line in instructions[:-1]:
            if m := re.fullmatch(
                r"(" + REG + r") = alloca \[(\d+) x i8\], align (\d+)", line
            ):
                q, n, a = m[1], int(m[2]), int(m[3])
                check(q not in memory and n == 136, "unknown stack slot")
                memory[q] = [None] * n
                alignment[q] = a
                pointers[q] = (q, 0)
            elif m := re.fullmatch(
                r"(?:tail )?call void @llvm.lifetime.(start|end).p0\(ptr nonnull ("
                + REG
                + r")\)",
                line,
            ):
                q = m[2]
                check(q in memory and q not in (state, buf), "invalid stack lifetime")
                if m[1] == "end":
                    del pointers[q]
                    del memory[q]
            elif m := re.fullmatch(
                r"("
                + REG
                + r") = getelementptr inbounds(?: nuw)? i8, ptr ("
                + REG
                + r"), i"
                + str(bits)
                + r" (\d+)",
                line,
            ):
                r, o = pointers[m[2]]
                off = o + int(m[3])
                check(off <= len(memory[r]), "out of bounds GEP")
                pointers[m[1]] = (r, off)
            elif m := re.fullmatch(
                r"("
                + REG
                + r") = load ("
                + LANES
                + "), ptr ("
                + REG
                + r"), align (\d+)",
                line,
            ):
                regs[m[1]] = read(m[3], 8 if m[2] == "i64" else 16, int(m[4]))
            elif m := re.fullmatch(
                r"(" + REG + r") = xor (" + LANES + ") (" + REG + "), (" + REG + ")",
                line,
            ):
                a, b = regs[m[3]], regs[m[4]]
                check(
                    len(a) == len(b) == (8 if m[2] == "i64" else 16),
                    "invalid vector xor",
                )
                regs[m[1]] = list(map(xor, a, b))
            elif m := re.fullmatch(
                r"(" + REG + r") = tail call i64 @llvm.bswap.i64\(i64 (" + REG + r")\)",
                line,
            ):
                value = regs[m[2]]
                check(len(value) == 8, "invalid bswap")
                regs[m[1]] = value[::-1]
            elif m := re.fullmatch(
                r"store (" + LANES + ") (" + REG + "), ptr (" + REG + r"), align (\d+)",
                line,
            ):
                value = regs[m[2]]
                check(len(value) == (8 if m[1] == "i64" else 16), "invalid store width")
                put(m[3], value, int(m[4]))
            elif m := re.fullmatch(
                r"(?:tail )?call void @llvm.memcpy.p0.p0.i"
                + str(bits)
                + r"\(ptr ([^,]+), ptr ([^,]+), i"
                + str(bits)
                + r" (\d+), i1 false\)",
                line,
            ):
                n = int(m[3])
                dst, da = pointer_arg(m[1], n)
                src, sa = pointer_arg(m[2], n)
                check(pointers[dst][0] != pointers[src][0], "overlapping copy")
                put(dst, read(src, n, sa), da)
            elif m := re.fullmatch(
                r"(?:tail )?call void @observed_keccak\(ptr ([^,]+)\)(?: #\d+)?", line
            ):
                q, a = pointer_arg(m[1], 200)
                check(
                    not called and read(q, 200, a) == initial,
                    "unexpected permutation input",
                )
                put(q, after, a)
                called = True
            else:
                raise ValueError("unknown rate-block instruction: " + line)
        if op == "absorb":
            expected = [
                xor(initial[i], block[logical[i]]) if i < 136 else initial[i]
                for i in range(200)
            ]
            check(
                not called and memory[state] == expected and memory[buf] == block,
                "incorrect absorption or modified input",
            )
        else:
            check(
                called
                and memory[state] == after
                and memory[buf] == [("state", i) for i in range(136)],
                "incorrect squeeze mapping",
            )
