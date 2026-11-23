"""Decode the SHA-256 and SHA-512 hardware loops emitted for the locked RustCrypto dependency.

The block argument has the Rust slice ABI, with disjoint live state, blocks and
stack. Accept only fully checked loads, stores, constant relocations, integer
loop control and the modeled SHA instructions. The two target assemblers spell
the same Armv8 register operations differently.
"""

import argparse
import re
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def decode(asm, apple, bits):
    small = bits == 256
    size = 64 if small else 128
    lanes = 4 if small else 2
    keys = 16 if small else 40
    initial = ["abcd", "efgh"] if small else ["ab", "cd", "ef", "gh"]
    marker = (
        f"sha{bits}11compress{bits}"
        if apple
        else f"sha{bits}12aarch64_sha{2 if small else 3}8compress"
    )
    (symbol,) = re.findall(r"^([^\s:]*" + marker + r"):$", asm, re.M)
    body = asm.split(symbol + ":\n", 1)[1].split("\t.cfi_endproc", 1)[0]
    lines = []
    for line in body.splitlines():
        line = line.strip()
        if (
            not line
            or line.startswith((".cfi_", ".loh ", ".size\t"))
            or re.fullmatch(r"Lloh\d+:|\.Lfunc_end\d+:", line)
        ):
            continue
        lines.append(re.sub(r"\s+", " ", line))
    saved = []
    for i in range(len(initial) // 2):
        m = re.fullmatch(
            r"ldp q(\d+), q(\d+), \[x0" + (", #32" if i else "") + r"\]", lines[i]
        )
        require(m, lines[i])
        saved.extend(m.groups())
    require(len(set(saved)) == len(initial), "state loads alias")
    num = len(initial) // 2
    m = re.fullmatch(r"cbz x2, (\.?LBB\d+_\d+)", lines[num])
    require(m, "empty input branch")
    empty = m[1]
    stores = [
        f"stp q{saved[2*i]}, q{saved[2*i+1]}, [x0" + (", #32]" if i else "]")
        for i in range(num)
    ]
    tail = [empty + ":", *stores, "ret"]
    require(lines[-len(tail) :] == tail, "state writeback")
    (loop_end,) = [i for i, l in enumerate(lines) if l.startswith("b.ne ")]
    loop = lines[loop_end].split()[1]
    loop_start = lines.index(loop + ":")
    require(loop_start < loop_end < len(lines) - 3, "loop branch")
    prologue = (
        ["stp d9, d8, [sp, #-16]!"]
        if apple
        else ["str d10, [sp, #-32]!", "stp d9, d8, [sp, #16]"]
    )
    epilogue = (
        ["ldp d9, d8, [sp], #16"]
        if apple
        else ["ldp d9, d8, [sp, #16]", "ldr d10, [sp], #32"]
    )
    if not small:
        prologue = (
            [
                "sub sp, sp, #496",
                "stp d15, d14, [sp, #416]",
                "stp d13, d12, [sp, #432]",
                "stp d11, d10, [sp, #448]",
                "stp d9, d8, [sp, #464]",
                "stp x28, x27, [sp, #480]",
            ]
            if apple
            else [
                "stp d15, d14, [sp, #-80]!",
                "stp d13, d12, [sp, #16]",
                "stp d11, d10, [sp, #32]",
                "stp d9, d8, [sp, #48]",
                "str x30, [sp, #64]",
                "sub sp, sp, #464",
            ]
        )
        epilogue = (
            [
                "ldp x28, x27, [sp, #480]",
                "ldp d9, d8, [sp, #464]",
                "ldp d11, d10, [sp, #448]",
                "ldp d13, d12, [sp, #432]",
                "ldp d15, d14, [sp, #416]",
                "add sp, sp, #496",
            ]
            if apple
            else [
                "add sp, sp, #464",
                "ldp d9, d8, [sp, #48]",
                "ldr x30, [sp, #64]",
                "ldp d11, d10, [sp, #32]",
                "ldp d13, d12, [sp, #16]",
                "ldp d15, d14, [sp], #80",
            ]
        )
    start = num + 1
    require(
        lines[start : start + len(prologue)] == prologue
        and lines[loop_end + 1 : -len(tail)] == epilogue,
        "ABI spill and restore",
    )
    prefix = lines[start + len(prologue) : loop_start]
    pages, constants, regs = {}, {}, dict(zip(saved, initial))
    spills = {}
    scratch = 0 if small else (416 if apple else 464)
    limit_reg = None
    for line in prefix:
        m = re.fullmatch(r"str q(\d+), \[sp(?:, #(\d+))?\]", line)
        if m:
            off = int(m[2] or 0)
            require(off % 16 == 0 and 0 <= off < scratch, line)
            spills[off] = regs[m[1]]
            continue
        m = re.fullmatch(r"adrp (x\d+), (\.?[lL]CPI\d+_\d+)(?:@PAGE)?", line)
        if m:
            require(m[1] not in [limit_reg, "x0", "x1", "x2"], line)
            pages[m[1]] = m[2]
            continue
        m = re.fullmatch(
            r"ldr q(\d+), \[(x\d+), (?::lo12:)?(\.?[lL]CPI\d+_\d+)(?:@PAGEOFF)?\]", line
        )
        if m:
            require(pages.get(m[2]) == m[3] and m[1] not in saved, line)
            directive = "(?:long|word)" if small else "(?:quad|xword)"
            (group,) = re.findall(
                r"^"
                + re.escape(m[3])
                + r":\n((?:\s*\."
                + directive
                + r"\s+-?\d+\n){"
                + str(lanes)
                + "})",
                asm,
                re.M,
            )
            words = [int(v) % 2 ** (128 // lanes) for v in re.findall(r"-?\d+", group)]
            require(all(w < 2 ** (128 // lanes) for w in words), line)
            i = int(m[3].rsplit("_", 1)[1])
            require(i not in constants and i < keys, line)
            regs[m[1]] = (
                f"({'slhdsa.vOf' if small else 'slhdsa.H512.vOf2'} pool {lanes*i})"
            )
            constants[i] = words
            continue
        m = re.fullmatch(r"add (x\d+), x1, x2, lsl #" + str(6 if small else 7), line)
        require(m and limit_reg is None and m[1] not in ["x0", "x1", "x2"], line)
        limit_reg = m[1]
        pages.pop(limit_reg, None)
    require(
        len(constants) == keys and limit_reg is not None,
        "round constants and end pointer",
    )
    initial_regs = dict(regs)
    written, inherited = set(), set()

    def read(q):
        if q not in written and q not in saved:
            inherited.add(q)
        return regs[q]

    code, used = [], []
    advanced = compared = False
    funcs = (
        {
            "add": "ADD",
            "sha256h": "SHA256H",
            "sha256h2": "SHA256H2",
            "sha256su0": "SHA256SU0",
            "sha256su1": "SHA256SU1",
        }
        if small
        else {
            "add": "ADD2",
            "ext": "EXT1",
            "sha512h": "SHA512H",
            "sha512h2": "SHA512H2",
            "sha512su0": "SHA512SU0",
            "sha512su1": "SHA512SU1",
        }
    )
    for line in lines[loop_start + 1 : loop_end]:
        if line == f"add x1, x1, #{size}":
            require(not advanced, line)
            advanced = True
            continue
        if line == "cmp x1, " + limit_reg:
            require(advanced and not compared, line)
            compared = True
            continue
        m = re.fullmatch(r"(ldr|ldp) q(\d+)(?:, q(\d+))?, \[sp(?:, #(\d+))?\]", line)
        if m:
            off = int(m[4] or 0)
            qs = [m[2]] if m[1] == "ldr" else [m[2], m[3]]
            require(
                (m[3] is not None) == (m[1] == "ldp") and len(set(qs)) == len(qs), line
            )
            for j, q in enumerate(qs):
                regs[q] = spills[off + 16 * j]
                written.add(q)
            continue
        m = re.fullmatch(r"ldp q(\d+), q(\d+), \[x1(?:, #(\d+))?\]", line)
        if m:
            require(
                not advanced and m[1] != m[2] and int(m[3] or 0) in range(0, size, 32),
                line,
            )
            written.update(m.groups()[:2])
            i = int(m[3] or 0) // 16
            regs[m[1]], regs[m[2]] = (i,), (i + 1,)
            continue
        op, operands = line.split(" ", 1)
        op, _, suffix = op.partition(".")
        ops = operands.split(", ")
        if op == "ext":
            require(not small and len(ops) == 4 and ops[-1] == "#8", line)
            ops.pop()
        ns = []
        for operand in ops:
            m = re.fullmatch(r"(v|q)(\d+)(?:\.(16b|4s|2d))?", operand)
            require(m and int(m[2]) < 32, operand)
            expected = (
                "16b"
                if op in ["rev32", "rev64", "mov", "ext"]
                else ("4s" if small else "2d")
            )
            first_q = (
                op in ["sha256h", "sha256h2", "sha512h", "sha512h2"] and len(ns) < 2
            )
            require(
                (m[1] == "q" if first_q else m[1] == "v")
                and (
                    suffix == expected and m[3] is None
                    if apple
                    else not suffix and (m[3] is None if first_q else m[3] == expected)
                ),
                line,
            )
            ns.append(m[2])
        dst = ns[0]
        if op == ("rev32" if small else "rev64"):
            require(len(ns) == 2 and isinstance(read(ns[1]), tuple), line)
            (i,) = regs[ns[1]]
            used.append(i)
            regs[dst] = f"m{i}"
        elif op == "mov":
            require(len(ns) == 2, line)
            regs[dst] = read(ns[1])
        else:
            require(
                op in funcs
                and len(ns) == (2 if op in ["sha256su0", "sha512su0"] else 3),
                line,
            )
            args = ns[1:] if op in ["add", "ext"] else ns
            require(all(isinstance(read(q), str) for q in args), line)
            v = f"t{len(code)}"
            fn = (
                f"plus {len(code)}" if not small and op == "add" else "Arm." + funcs[op]
            )
            code.append(f"  let {v} := {fn} " + " ".join(regs[q] for q in args))
            regs[dst] = v
        written.add(dst)
    require(
        all(regs[q] == initial_regs[q] for q in inherited),
        "loop clobbers a retained constant",
    )
    require(
        advanced and compared and sorted(used) == list(range(size // 16)),
        "full block and loop condition",
    )
    return [word for i in range(keys) for word in constants[i]], (
        code + ["  (" + ", ".join(regs[q] for q in saved) + ")"]
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("linux", type=Path)
    parser.add_argument("apple", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--bits", choices=[256, 512], type=int, default=256)
    args = parser.parse_args()
    small = args.bits == 256
    text = [
        "-- Generated by scripts/check-rustcrypto-arm-code.py from both release targets.",
        (
            "import Slhdsa.Proofs.Hw.Model"
            if small
            else "import Slhdsa.Proofs.Hw512.Rounds"
        ),
        "",
        "namespace slhdsa.RcArmCode" + ("" if small else ".S512"),
        "",
    ]
    for name, path in [("linux", args.linux), ("apple", args.apple)]:
        pool, code = decode(path.read_text(), name == "apple", args.bits)
        text += [f"def {name}Constants : List (BitVec {32 if small else 64}) := ["]
        text += [
            "  "
            + ", ".join(str(x) for x in pool[i : i + 4])
            + ("," if i + 4 < len(pool) else "]")
            for i in range(0, len(pool), 4)
        ]
        params = (
            "abcd efgh m0 m1 m2 m3 : Arm.V"
            if small
            else "ab cd ef gh m0 m1 m2 m3 m4 m5 m6 m7 : Arm.V2"
        )
        result = "Arm.V × Arm.V" if small else "Arm.V2 × Arm.V2 × Arm.V2 × Arm.V2"
        arg = "" if small else " (plus : Nat → Arm.V2 → Arm.V2 → Arm.V2)"
        text += [
            "",
            f"def {name}{arg} (pool : List (BitVec {32 if small else 64})) ({params}) : {result} :=",
            *code,
            "",
        ]
    args.output.write_text(
        "\n".join([*text, "end slhdsa.RcArmCode" + ("" if small else ".S512"), ""])
    )


if __name__ == "__main__":
    main()
