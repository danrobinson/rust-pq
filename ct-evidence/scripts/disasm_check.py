#!/usr/bin/env python3
"""Static facts about the native (aarch64-apple-darwin, release) machine code
of the slhdsa crate.

Usage: disasm_check.py <linked binary> [<rlib A> <rlib B>]

Part 1 (linked binary): for every function of the slhdsa crate, instruction
count, conditional branches, indirect branches, and whether it contains
integer division, SHA/AES crypto-extension or SIMD instructions; the calls
that leave the crate; then, for the functions that contain the SHA-256
compression code, every conditional branch together with the instruction that
sets its condition, and the register-indexed loads.

Part 2 (optional): compare the slhdsa object code inside two rlibs (the one
built as a dependency of ct-evidence and one built from the main crate's own
manifest with `cargo build --release`), function by function, after
normalising the crate disambiguator hashes in symbol names and the per-build
hash in the names of anonymous constants (`l_anon.<hash>.N`, e.g. panic
locations).
"""
import re, subprocess, sys, collections

def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True).stdout

def objdump(path, extra=()):
    return run(["objdump", "-d", "--no-show-raw-insn", *extra, path])

def ident_list(s):
    """The length-prefixed identifiers at the start of s (v0 mangling)."""
    out = []
    while True:
        m = re.match(r"(\d+)_?", s)
        if not m:
            break
        n = int(m.group(1))
        s = s[m.end():]
        if len(s) < n:
            break
        out.append(s[:n]); s = s[n:]
    return out

def short(sym):
    """Crude v0 demangling: enough to name the crate's functions readably."""
    i = sym.find("_6slhdsa")
    if i < 0:
        return sym
    pre = sym[:i]
    rest = sym[i + 1:]                       # "6slhdsa..."
    path = ident_list(rest)
    if re.match(r"^_?_RNvNt", pre) and len(path) > 1:
        return "::".join(path)               # a plain function of the crate
    # an instantiation of a generic from another crate, owned by slhdsa
    ids = [x for x in re.findall(r"\d+_?([A-Za-z_][A-Za-z_0-9]*?)(?=\d|[A-Z]|$)", pre) if len(x) > 2]
    return "<instantiation in slhdsa> " + "::".join(ids[-3:])

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
CSEL = ("csel", "csinc", "csinv", "csneg", "cset", "csetm", "cinc", "cinv", "cneg", "ccmp", "ccmn")

def branch_table(ins):
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
                for j in range(i - 1, max(i - 8, -1), -1):
                    if ins[j][1] in ("cmp", "cmn", "subs", "adds", "tst", "ands", "ccmp", "ccmn", "fcmp"):
                        setter = ins[j][1] + " " + re.sub(r"\s*;.*", "", ins[j][2])
                        if ins[j][1] in ("ccmp", "ccmn"):
                            for k in range(j - 1, max(j - 8, -1), -1):
                                if ins[k][1] in ("cmp", "cmn", "subs", "adds", "tst", "ands"):
                                    setter = ins[k][1] + " " + re.sub(r"\s*;.*", "", ins[k][2]) + " ; " + setter
                                    break
                        break
            else:
                setter = mn + " " + ",".join(ops.split(",")[:-1])
            # abstract registers so identical checks group together
            key = (mn, re.sub(r"\b[xw]\d+\b", "R", setter), "backward (loop)" if back else "forward")
            pat[key] += 1
    print("| branch | condition set by (registers abstracted to R) | direction | count |")
    print("|---|---|---|---|")
    for (mn, setter, d), n in sorted(pat.items(), key=lambda x: (-x[1], x[0])):
        print(f"| `{mn}` | `{setter}` | {d} | {n} |")

def indexed_loads(ins):
    mem = [(mn, ops) for _, mn, ops in ins if re.match(r"^(ldr|ldrb|ldur|ldp|ldrh|str|strb|strh|stur|stp)$", mn) and re.search(r"\[x\d+, [xw]\d+", ops)]
    c = collections.Counter((m, re.sub(r"\s*;.*", "", o)) for m, o in mem)
    if not c:
        print("- none")
    for (mn, ops), n in c.most_common():
        print(f"- `{mn} {ops}` x{n}")

def stub_table(binary):
    """address of each import stub -> imported symbol (from the indirect symbol table)."""
    res = {}
    on = False
    for line in run(["otool", "-Iv", binary]).splitlines():
        if line.startswith("Indirect symbols for"):
            on = "__stubs" in line
            continue
        m = re.match(r"^0x([0-9a-f]+)\s+\d+\s+(\S+)$", line.strip())
        if on and m:
            res[int(m.group(1), 16)] = m.group(2)
    return res

def callee(ops, stubs={}):
    """Name of the function a bl/b operand refers to."""
    m = re.match(r"^0x([0-9a-f]+)", ops.strip())
    if m and int(m.group(1), 16) in stubs:
        return stubs[int(m.group(1), 16)]
    m = re.search(r"<([^>+]+)(\+0x[0-9a-f]+)?>", ops)
    return m.group(1) if m else None

def part1(binary):
    funcs = functions(objdump(binary))
    mine = collections.OrderedDict((k, v) for k, v in funcs.items() if "_6slhdsa" in k)
    print(f"## Static summary of slhdsa functions in {binary}\n")
    print("| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |")
    print("|---|---|---|---|---|---|---|---|")
    tot = collections.Counter()
    rows = []
    for k, ins in mine.items():
        c = collections.Counter()
        for _, mn, ops in ins:
            if COND.match(mn): c["cond"] += 1
            if mn in ("br", "blr"): c["ind"] += 1
            if mn in ("udiv", "sdiv"): c["div"] += 1
            if CRYPTO.match(mn): c["crypto"] += 1
            if SIMD_OP.search(ops.split(";")[0]): c["simd"] += 1
            if mn in CSEL: c["csel"] += 1
        tot.update(c); tot["insns"] += len(ins)
        rows.append((short(k), len(ins), c))
    for name, n, c in sorted(rows, key=lambda r: r[0]):
        print(f"| `{name}` | {n} | {c['cond']} | {c['ind']} | {c['div']} | {c['crypto']} | {c['simd']} | {c['csel']} |")
    print(f"| **total ({len(rows)} functions)** | {tot['insns']} | {tot['cond']} | {tot['ind']} | {tot['div']} | {tot['crypto']} | {tot['simd']} | {tot['csel']} |")
    print()
    # crypto-extension and SIMD instructions used anywhere in slhdsa code
    simd = collections.Counter(); crypto = collections.Counter()
    for k, ins in mine.items():
        for _, mn, ops in ins:
            if CRYPTO.match(mn):
                crypto[mn] += 1
            elif SIMD_OP.search(ops.split(";")[0]):
                simd[mn] += 1
    print("Crypto-extension instructions in slhdsa code (mnemonic: count):",
          ", ".join(f"{m}: {n}" for m, n in crypto.most_common()) or "none")
    print()
    print("Other SIMD/FP-register instructions in slhdsa code (mnemonic: count):",
          ", ".join(f"{m}: {n}" for m, n in simd.most_common()) or "none")
    print()
    # calls that leave the crate
    ext = collections.Counter()
    stubs = stub_table(binary)
    for k, ins in mine.items():
        for _, mn, ops in ins:
            if mn in ("bl", "b"):
                c = callee(ops, stubs)
                if c and "_6slhdsa" not in c and c != k:
                    ext[c] += 1
    def pretty(c):
        m = re.search(r"(\d+)(___rust_\w+|handle_error|panic_bounds_check|slice_index_fail|len_mismatch_fail|panic_\w+|grow_one\w*)$", c)
        return m.group(2).lstrip("_") if m else c
    agg = collections.Counter()
    for c, n in ext.items():
        agg[pretty(c)] += n
    print("Call sites in slhdsa code whose target is outside the crate (target: sites):",
          ", ".join(f"`{c}`: {n}" for c, n in sorted(agg.items(), key=lambda x: (-x[1], x[0]))) or "none")
    cmpcalls = sum(n for c, n in agg.items() if re.search(r"memcmp|bcmp", c))
    print(f"\nCalls of `memcmp`/`bcmp` from slhdsa code: {cmpcalls}.\n")
    # the functions that contain the compression code
    kernel = ["slhdsa::sha256::schedule", "slhdsa::sha256::sha256_from", "slhdsa::hash::chain_blocks", "slhdsa::hash::chain_blocks_portable",
              "slhdsa::hash::thash_short", "slhdsa::hash::thash_values", "slhdsa::hash::seed_ctx", "slhdsa::hash::prf_msg"]
    for want in kernel:
        hits = [(k, v) for k, v in mine.items() if short(k) == want]
        if not hits:
            print(f"### `{want}`: no out-of-line copy in this binary\n")
            continue
        k, ins = hits[0]
        ncr = sum(1 for _, mn, _ in ins if CRYPTO.match(mn))
        print(f"### Conditional branches in `{want}` ({len(ins)} instructions, {ncr} crypto-extension)\n")
        if len(ins) <= 2:
            print("(a tail jump to `" + (short(callee(ins[-1][2]) or "?")) + "`)\n")
            continue
        branch_table(ins)
        print(f"\nRegister-indexed loads and stores in `{want}` (base + index register):\n")
        indexed_loads(ins)
        print()

def member_symbols(path):
    """archive member -> {address: first non-temporary text symbol there}."""
    res = {}
    cur = None
    for line in run(["nm", "-n", path]).splitlines():
        m = re.match(r"^(\S+\.o):$", line.strip())
        if m:
            cur = m.group(1); res[cur] = {}
            continue
        m = re.match(r"^([0-9a-f]+) [tT] (\S+)$", line.strip())
        if m and cur is not None and not m.group(2).startswith("ltmp"):
            res[cur].setdefault(int(m.group(1), 16), m.group(2))
    return res

def norm_name(s):
    s = re.sub(r"Cs[0-9A-Za-z]+_6slhdsa", "6slhdsa", s)
    s = re.sub(r"Cs[0-9A-Za-z]+_", "Cs_", s)          # other crates' disambiguators
    s = re.sub(r"\.llvm\.\d+", ".llvm", s)             # per-build suffix of promoted local symbols
    return s

def norm_obj(path):
    """function name (hash-normalised) -> list of normalised instruction strings, from an rlib.

    The assembler labels the start of every object file `ltmp0`, and the
    disassembler prints that label instead of the function that starts there;
    the real name is taken from the symbol table."""
    syms = member_symbols(path)
    text = objdump(path, ["-r"])
    res = {}
    cur = None
    member = None
    for line in text.splitlines():
        m = re.match(r"^.*\(([^()]+\.o)\):\s+file format", line)
        if m:
            member = m.group(1); cur = None
            continue
        m = re.match(r"^([0-9a-f]+) <(.+)>:$", line)
        if m:
            name = m.group(2)
            if name.startswith("ltmp"):
                name = syms.get(member, {}).get(int(m.group(1), 16), member + ":" + name)
            cur = norm_name(name); res.setdefault(cur, [])
            continue
        line = norm_name(line)
        line = re.sub(r"\b_?(l_)?anon\.[0-9a-f]+\.", "anon.", line)  # anonymous constants (names carry a per-build hash)
        m = re.match(r"^\s*[0-9a-f]+:\s+(.*)$", line)
        if m and cur is not None:
            t = m.group(1)
            t = re.sub(r"0x[0-9a-f]+ <([^>+]+)(\+0x[0-9a-f]+)?>", lambda mm: "<" + mm.group(1) + (mm.group(2) or "") + ">", t)
            t = re.sub(r"\bl_?[A-Za-z_.]*\d+\b", "L", t)       # local labels
            res[cur].append(re.sub(r"\s+", " ", t.strip()))
    return res

def const_data(path):
    """Contents of the constant-data sections of an rlib's object files, per section in member order:
    list of (section, bytes as hex). Object files are unlinked, so the bytes do not depend on addresses."""
    res = []
    cur = None
    for line in run(["objdump", "-s", "-j", "__const", "-j", "__literal16", "-j", "__literal8", "-j", "__literal4", "-j", "__cstring", path]).splitlines():
        m = re.match(r"^Contents of section (\S+):", line)
        if m:
            cur = [m.group(1), ""]; res.append(cur)
            continue
        m = re.match(r"^\s*[0-9a-f]+ ((?:[0-9a-f]+ ?)+)", line)
        if m and cur is not None:
            cur[1] += m.group(1).replace(" ", "")
    return [(a, b) for a, b in res]

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
    unnamed = [k for k in set(fa) | set(fb) if ":ltmp" in k]
    print("Constant-data sections of the object files (`__const`, `__literal*`, `__cstring`; unlinked, so independent of addresses):\n")
    ca, cb = const_data(a), const_data(b)
    ok = len(ca) == len(cb)
    if not ok:
        print(f"- **different number of sections: {len(ca)} vs {len(cb)}**")
    plen = None
    for (sa, ha), (sb, hb) in zip(ca, cb):
        ba, bb = bytes.fromhex(ha), bytes.fromhex(hb)
        if sa != sb:
            ok = False; print(f"- **section order differs: {sa} vs {sb}**")
        elif ba == bb:
            print(f"- `{sa}`: {len(ba)} bytes, identical")
        elif sa.endswith("__cstring"):
            # source-file paths of panic locations: absolute when the crate is built as a
            # path dependency, relative when built from its own directory
            xa, xb = ba.split(b"\0"), bb.split(b"\0")
            strip = lambda x: x[x.rfind(b"/src/") + 1:] if b"/src/" in x else x
            if [strip(x) for x in xa] == [strip(x) for x in xb]:
                plens = {len(x) - len(y) for x, y in zip(xa, xb) if x != y}
                plen = plens.pop() if len(plens) == 1 else None
                print(f"- `{sa}`: {len(xa) - 1} strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory ({plen} bytes longer each)")
            else:
                ok = False; print(f"- **`{sa}` differs**")
        elif len(ba) == len(bb) and len(ba) % 8 == 0 and plen is not None:
            wa = [int.from_bytes(ba[i:i + 8], "little") for i in range(0, len(ba), 8)]
            wb = [int.from_bytes(bb[i:i + 8], "little") for i in range(0, len(bb), 8)]
            d = [(x, y) for x, y in zip(wa, wb) if x != y]
            if all(x - y == plen for x, y in d):
                print(f"- `{sa}`: {len(ba)} bytes, identical except {len(d)} 8-byte fields that are larger in A by exactly {plen}: the lengths of those path strings in the panic-location records")
            else:
                ok = False; print(f"- **`{sa}` differs**")
        else:
            ok = False; print(f"- **`{sa}` differs**")
    print("\nconstant data: " + ("same numeric constants and tables in A and B." if ok else "**DIFFERENT between A and B.**"))
    print(f"\n{same} functions identical instruction-for-instruction (incl. relocation targets), {diff} different, {missing} present in only one; {na} disassembly lines (instructions + relocation records) compared in A; {len(unnamed)} code ranges left unnamed.\n")

if __name__ == "__main__":
    part1(sys.argv[1])
    if len(sys.argv) >= 4:
        part2(sys.argv[2], sys.argv[3])
