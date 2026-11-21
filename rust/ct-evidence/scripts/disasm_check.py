#!/usr/bin/env python3
"""Static facts about the native (aarch64-apple-darwin, release) machine code
of the slhdsa crate.

Usage: disasm_check.py <linked binary> [<rlib A> <rlib B>]

Part 1 (linked binary): for every function of the slhdsa crate, instruction
count, conditional branches, indirect branches, calls, and whether it contains
integer division, SHA/AES crypto-extension or SIMD instructions; then a
listing of every conditional branch in `sha256` together with the instruction
that sets its condition.

Part 2 (optional): compare the slhdsa object code inside two rlibs (the one
built as a dependency of ct-evidence and the one built by `cargo ... --release`
in the main crate), function by function, after normalising the crate
disambiguator hashes in symbol names and the per-build hash in the names of
anonymous constants (`l_anon.<hash>.N`, e.g. panic locations).
"""
import re, subprocess, sys, collections

def objdump(path, extra=()):
    return subprocess.run(["objdump", "-d", "--no-show-raw-insn", *extra, path],
                          capture_output=True, text=True).stdout

def short(sym):
    """Crude v0 demangling: the length-prefixed identifiers after the crate name."""
    i = sym.find("_6slhdsa")
    if i < 0:
        return sym
    pre = sym[:i]
    rest = sym[i + 8:]
    out = []
    while True:
        m = re.match(r"(\d+)", rest)
        if not m:
            break
        n = int(m.group(1)); rest = rest[len(m.group(1)):]
        if rest.startswith("_"):
            rest = rest[1:]
        out.append(rest[:n]); rest = rest[n:]
    name = "slhdsa::" + "::".join(out) if out else "slhdsa"
    if not sym.endswith(tuple(out[-1:])) or "RINv" in pre or "RNvM" in pre:
        # generic instantiation owned by the crate (alloc::raw_vec etc.)
        ids = re.findall(r"\d+([a-z_][A-Za-z_0-9]*?)(?=\d|[A-Z]|$)", pre)
        if "raw_vec" in pre:
            name = "<alloc::raw_vec instantiation in slhdsa> " + (ids[-1] if ids else "")
    return name

def functions(text):
    funcs = collections.OrderedDict()
    cur = None
    for line in text.splitlines():
        m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if m:
            cur = m.group(1); funcs[cur] = []
            continue
        m = re.match(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
        if m and cur is not None:
            funcs[cur].append((int(m.group(1), 16), m.group(2), m.group(3)))
    return funcs

COND = re.compile(r"^(b\.\w+|cbz|cbnz|tbz|tbnz)$")
CRYPTO = re.compile(r"^(sha\d|aes|pmull|sm3|sm4|rax1|eor3|bcax|xar)")
SIMD_OP = re.compile(r"\b([vqd]\d+|z\d+)\b")

def part1(binary):
    funcs = functions(objdump(binary))
    mine = {k: v for k, v in funcs.items() if "_6slhdsa" in k}
    print(f"## Static summary of slhdsa functions in {binary}\n")
    print("| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |")
    print("|---|---|---|---|---|---|---|---|")
    tot = collections.Counter()
    for k, ins in mine.items():
        c = collections.Counter()
        for _, mn, ops in ins:
            if COND.match(mn): c["cond"] += 1
            if mn in ("br", "blr"): c["ind"] += 1
            if mn in ("udiv", "sdiv"): c["div"] += 1
            if CRYPTO.match(mn): c["crypto"] += 1
            if SIMD_OP.search(ops.split(";")[0]): c["simd"] += 1
            if mn in ("csel", "csinc", "csinv", "csneg", "cset", "csetm", "cinc", "ccmp", "ccmn"): c["csel"] += 1
        tot.update(c); tot["insns"] += len(ins)
        print(f"| `{short(k)}` | {len(ins)} | {c['cond']} | {c['ind']} | {c['div']} | {c['crypto']} | {c['simd']} | {c['csel']} |")
    print(f"| **total** | {tot['insns']} | {tot['cond']} | {tot['ind']} | {tot['div']} | {tot['crypto']} | {tot['simd']} | {tot['csel']} |")
    print()
    # SIMD instructions used anywhere in slhdsa code
    simd = collections.Counter()
    for k, ins in mine.items():
        for _, mn, ops in ins:
            if SIMD_OP.search(ops.split(";")[0]):
                simd[mn] += 1
    print("SIMD/FP-register instructions used in slhdsa code (mnemonic: count):",
          ", ".join(f"{m}: {n}" for m, n in simd.most_common()) or "none")
    print()
    sha = [v for k, v in mine.items() if k.endswith("6sha2566sha256")]
    if sha:
        ins = sha[0]
        print("### Conditional branches inside the compiled `sha256` (compress/schedule/pad are inlined into it)\n")
        pat = collections.Counter()
        for i, (a, mn, ops) in enumerate(ins):
            if COND.match(mn):
                tgt = ops.split("<")[0].strip().split(",")[-1].strip()
                try:
                    back = int(tgt, 16) <= a
                except ValueError:
                    back = False
                # the flag-setting instruction is the closest preceding cmp/subs/tst/..., or the operand itself for cbz/tbz
                setter = ""
                if mn.startswith("b."):
                    for j in range(i - 1, max(i - 6, -1), -1):
                        if ins[j][1] in ("cmp", "cmn", "subs", "adds", "tst", "ands", "ccmp"):
                            setter = ins[j][1] + " " + re.sub(r"\s*;.*", "", ins[j][2])
                            break
                else:
                    setter = mn + " " + ops.split(",")[0]
                # abstract registers so identical checks group together
                key = (mn, re.sub(r"\b[xw]\d+\b", "R", setter), "backward (loop)" if back else "forward")
                pat[key] += 1
        print("| branch | condition set by (registers abstracted to R) | direction | count |")
        print("|---|---|---|---|")
        for (mn, setter, d), n in sorted(pat.items(), key=lambda x: -x[1]):
            print(f"| `{mn}` | `{setter}` | {d} | {n} |")
        mem = [(mn, ops) for _, mn, ops in ins if re.match(r"^(ldr|ldrb|ldur|ldp|ldrh)$", mn) and re.search(r"\[x\d+, x\d+", ops)]
        print("\nRegister-indexed loads in `sha256` (base + index register):\n")
        for mn, ops in collections.Counter(mem).most_common():
            pass
        for (mn, ops), n in collections.Counter((m, re.sub(r"\s*;.*", "", o)) for m, o in mem).most_common():
            print(f"- `{mn} {ops}` x{n}")
        print()

def norm_obj(path):
    """function name (hash-normalised) -> list of normalised instruction strings, from an rlib."""
    text = objdump(path, ["-r"])
    res = {}
    cur = None
    for line in text.splitlines():
        line = re.sub(r"Cs[0-9A-Za-z]+_6slhdsa", "6slhdsa", line)
        line = re.sub(r"Cs[0-9A-Za-z]+_", "Cs_", line)       # other crates' disambiguators
        line = re.sub(r"l_anon\.[0-9a-f]+\.", "l_anon.", line)  # anonymous constants (names carry a per-build hash)
        m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if m:
            cur = m.group(1); res.setdefault(cur, [])
            continue
        m = re.match(r"^\s*[0-9a-f]+:\s+(.*)$", line)
        if m and cur is not None:
            t = m.group(1)
            t = re.sub(r"0x[0-9a-f]+ <([^>+]+)(\+0x[0-9a-f]+)?>", lambda mm: "<" + mm.group(1) + (mm.group(2) or "") + ">", t)
            t = re.sub(r"\bl_?[A-Za-z_.]*\d+\b", "L", t)       # local labels
            res[cur].append(re.sub(r"\s+", " ", t.strip()))
    return res

def part2(a, b):
    fa, fb = norm_obj(a), norm_obj(b)
    print(f"## Object-code comparison of slhdsa\n\n- A: `{a}`\n- B: `{b}`\n")
    names = sorted(k for k in set(fa) | set(fb) if "6slhdsa" in k)
    same = diff = missing = 0
    for k in names:
        if k not in fa or k not in fb:
            missing += 1; print(f"- only in {'A' if k in fa else 'B'}: `{k}`")
        elif fa[k] == fb[k]:
            same += 1
        else:
            diff += 1; print(f"- DIFFERENT code: `{k}` ({len(fa[k])} vs {len(fb[k])} instructions)")
    na = sum(len(fa[k]) for k in names if k in fa)
    print(f"\n{same} functions identical instruction-for-instruction (incl. relocation targets), {diff} different, {missing} present in only one; {na} disassembly lines (instructions + relocation records) compared in A.\n")

if __name__ == "__main__":
    part1(sys.argv[1])
    if len(sys.argv) >= 4:
        part2(sys.argv[2], sys.argv[3])
