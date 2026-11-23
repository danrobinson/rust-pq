"""Decode the SHA-256 hardware loop emitted for the locked RustCrypto dependency.

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


def decode(asm, apple):
    marker = "sha25611compress256" if apple else "sha25612aarch64_sha28compress"
    symbol, = re.findall(r"^([^\s:]*" + marker + r"):$", asm, re.M)
    body = asm.split(symbol + ":\n", 1)[1].split("\t.cfi_endproc", 1)[0]
    lines = []
    for line in body.splitlines():
        line = line.strip()
        if not line or line.startswith((".cfi_", ".loh ", ".size\t")) or re.fullmatch(r"Lloh\d+:|\.Lfunc_end\d+:", line):
            continue
        lines.append(re.sub(r"\s+", " ", line))
    require(lines[0].startswith("ldp ") and lines[1].startswith("cbz x2, "), "state load and empty input branch")
    state_load = re.fullmatch(r"ldp q(\d+), q(\d+), \[x0\]", lines[0])
    require(state_load and state_load[1] != state_load[2], lines[0])
    saved = state_load.groups()
    empty = lines[1].split(", ")[1]
    require(lines[-3:] == [empty + ":", "stp q%s, q%s, [x0]" % saved, "ret"], "state writeback")
    loop_end, = [i for i, l in enumerate(lines) if l.startswith("b.ne ")]
    loop = lines[loop_end].split()[1]
    loop_start = lines.index(loop + ":")
    require(loop_start < loop_end < len(lines) - 3, "loop branch")
    prologue = ["stp d9, d8, [sp, #-16]!"] if apple else ["str d10, [sp, #-32]!", "stp d9, d8, [sp, #16]"]
    epilogue = ["ldp d9, d8, [sp], #16"] if apple else ["ldp d9, d8, [sp, #16]", "ldr d10, [sp], #32"]
    require(lines[2:2 + len(prologue)] == prologue and lines[loop_end+1:-3] == epilogue, "ABI spill and restore")
    prefix = lines[2 + len(prologue):loop_start]
    pages, constants, regs = {}, {}, dict(zip(saved, ["abcd", "efgh"]))
    limit_reg = None
    for line in prefix:
        m = re.fullmatch(r"adrp (x\d+), (\.?[lL]CPI\d+_\d+)(?:@PAGE)?", line)
        if m:
            require(m[1] not in [limit_reg, "x0", "x1", "x2"], line)
            pages[m[1]] = m[2]
            continue
        m = re.fullmatch(r"ldr q(\d+), \[(x\d+), (?::lo12:)?(\.?[lL]CPI\d+_\d+)(?:@PAGEOFF)?\]", line)
        if m:
            require(pages.get(m[2]) == m[3] and m[1] not in regs, line)
            group, = re.findall(r"^" + re.escape(m[3]) + r":\n((?:\s*\.(?:long|word)\s+\d+\n){4})", asm, re.M)
            words = list(map(int, re.findall(r"\d+", group)))
            require(all(w < 2**32 for w in words), line)
            i = int(m[3].rsplit("_", 1)[1])
            require(i not in constants and i < 16, line)
            regs[m[1]] = f"(slhdsa.vOf pool {4*i})"
            constants[i] = words
            continue
        m = re.fullmatch(r"add (x\d+), x1, x2, lsl #6", line)
        require(m and limit_reg is None and m[1] not in ["x0", "x1", "x2"], line)
        limit_reg = m[1]
        pages.pop(limit_reg, None)
    require(len(constants) == 16 and limit_reg is not None, "round constants and end pointer")
    frozen = set(regs) - set(saved)
    code, used = [], []
    advanced = compared = False
    funcs = {"add": "ADD", "sha256h": "SHA256H", "sha256h2": "SHA256H2",
             "sha256su0": "SHA256SU0", "sha256su1": "SHA256SU1"}
    for line in lines[loop_start + 1:loop_end]:
        if line == "add x1, x1, #64":
            require(not advanced, line)
            advanced = True
            continue
        if line == "cmp x1, " + limit_reg:
            require(advanced and not compared, line)
            compared = True
            continue
        m = re.fullmatch(r"ldp q(\d+), q(\d+), \[x1(?:, #(32))?\]", line)
        if m:
            require(not advanced and not (set(m.groups()[:2]) & frozen), line)
            i = int(m[3] or 0)//16
            regs[m[1]], regs[m[2]] = (i,), (i+1,)
            continue
        op, operands = line.split(" ", 1)
        op, _, suffix = op.partition(".")
        ops = operands.split(", ")
        ns = []
        for operand in ops:
            m = re.fullmatch(r"(v|q)(\d+)(?:\.(16b|4s))?", operand)
            require(m and int(m[2]) < 32, operand)
            expected = "16b" if op in ["rev32", "mov"] else "4s"
            first_q = op in ["sha256h", "sha256h2"] and len(ns) < 2
            require((m[1] == "q" if first_q else m[1] == "v") and
                    (suffix == expected and m[3] is None if apple else
                     not suffix and (m[3] is None if first_q else m[3] == expected)), line)
            ns.append(m[2])
        dst = ns[0]
        require(dst not in frozen, line)
        if op == "rev32":
            require(len(ns) == 2 and isinstance(regs[ns[1]],tuple), line)
            i, = regs[ns[1]]
            used.append(i)
            regs[dst] = f"m{i}"
        elif op == "mov":
            require(len(ns) == 2, line)
            regs[dst] = regs[ns[1]]
        else:
            require(op in funcs and len(ns) == (2 if op == "sha256su0" else 3), line)
            args = ns[1:] if op == "add" else ns
            require(all(isinstance(regs[q], str) for q in args), line)
            v = f"t{len(code)}"
            code.append(f"  let {v} := Arm.{funcs[op]} " + " ".join(regs[q] for q in args))
            regs[dst] = v
    require(advanced and compared and sorted(used) == list(range(4)), "full block and loop condition")
    return [word for i in range(16) for word in constants[i]], (code + [f"  ({regs[saved[0]]}, {regs[saved[1]]})"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("linux", type=Path)
    parser.add_argument("apple", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    text = ["-- Generated by scripts/check-rustcrypto-arm-code.py from both release targets.",
            "import Slhdsa.Proofs.Hw.Model", "", "namespace slhdsa.RcArmCode", ""]
    for name, path in [("linux", args.linux), ("apple", args.apple)]:
        pool, code = decode(path.read_text(), name == "apple")
        text += [f"def {name}Constants : List (BitVec 32) := ["]
        text += ["  " + ", ".join(str(x) for x in pool[i:i+4]) + ("," if i+4<len(pool) else "]") for i in range(0,len(pool),4)]
        text += ["", f"def {name} (pool : List (BitVec 32)) (abcd efgh m0 m1 m2 m3 : Arm.V) : Arm.V × Arm.V :=", *code, ""]
    args.output.write_text("\n".join([*text,"end slhdsa.RcArmCode",""]))


if __name__ == "__main__":
    main()
