#!/usr/bin/env python3
"""Compare every output byte symbolically in the optimized public-key extraction IR."""
import argparse
from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REG = r"%[\w.]+"
TARGETS = ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"]


def origin_map(ir, name, n):
    alias = re.search(rf"^@{name} = unnamed_addr alias void \(ptr, ptr\), ptr @(\w+)$", ir, re.M)
    if alias:
        return origin_map(ir, alias[1], n)
    match = re.search(rf"^define void @{name}\(([^\n]+)\{{\n([^}}]+)^}}", ir, re.M)
    if not match or f"sret([{2*n} x i8])" not in match[1] or f"dereferenceable({4*n}) %k)" not in match[1]:
        raise ValueError(f"unsupported ABI for {name}")
    # Each distinct integer denotes an independent symbolic input byte.
    memory = {"%k": list(range(4*n)), "%_0": [None]*(2*n)}
    alignment = {k: 1 for k in memory}
    pointers = {k: (k, 0) for k in memory}
    lines = match[2].strip().splitlines()
    if not lines[0].endswith(":") or lines[-1].strip() != "ret void":
        raise ValueError("expected straight-line returning function")
    for line in map(str.strip, lines[1:-1]):
        if m := re.fullmatch(rf"({REG}) = alloca \[(\d+) x i8\], align (\d+)", line):
            memory[m[1]] = [None]*int(m[2])
            alignment[m[1]] = int(m[3])
            pointers[m[1]] = (m[1], 0)
        elif m := re.fullmatch(rf"({REG}) = getelementptr inbounds nuw i8, ptr ({REG}), i64 (\d+)", line):
            base, offset = pointers[m[2]]
            offset += int(m[3])
            if offset > len(memory[base]):
                raise ValueError("out-of-bounds pointer")
            pointers[m[1]] = (base, offset)
        elif m := re.fullmatch(rf"call void @llvm\.lifetime\.(start|end)\.p0\(ptr nonnull ({REG})\)", line):
            if m[2] in ("%_0", "%k") or pointers[m[2]] != (m[2], 0):
                raise ValueError("unexpected lifetime operand")
            memory[m[2]] = [None]*len(memory[m[2]]) if m[1] == "start" else []
        elif m := re.fullmatch(rf"(?:tail )?call void @llvm\.memcpy\.p0\.p0\.i64\(ptr noundef nonnull align (?P<da>\d+) dereferenceable\((?P<dn>\d+)\) (?P<dst>{REG}), ptr noundef nonnull (?:readonly )?align (?P<sa>\d+) dereferenceable\((?P<sn>\d+)\) (?P<src>{REG}), i64 (?P<size>\d+), i1 false\)(?:, !noalias !\d+)?", line):
            dst, d = pointers[m["dst"]]
            src, s = pointers[m["src"]]
            size = int(m["size"])
            for base, offset, a in ((src,s,int(m["sa"])), (dst,d,int(m["da"]))):
                if alignment[base] % a or offset % a:
                    raise ValueError("misaligned copy")
            if (dst == "%k" or d + max(size, int(m["dn"])) > len(memory[dst])
                    or s + max(size, int(m["sn"])) > len(memory[src])
                    or (dst == src and max(d,s) < min(d,s)+size)):
                raise ValueError("invalid copy")
            data = memory[src][s:s+size]
            if None in data:
                raise ValueError("uninitialized read")
            memory[dst][d:d+size] = data
        else:
            raise ValueError(f"unmodeled instruction in {name}: {line}")
    return memory["%_0"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", action="append", choices=TARGETS)
    targets = parser.parse_args().target or TARGETS
    sets = [(f"{family}_{strength}{mode}", strength//8)
            for family in ("sha2","shake") for strength in (128,192,256) for mode in "sf"]
    with tempfile.TemporaryDirectory() as directory:
        p = Path(directory)
        (p/"Cargo.toml").write_text('[package]\nname="relproof"\nversion="0.1.0"\nedition="2021"\n'
            '[dependencies]\nslh-dsa="=0.2.0-rc.5"\nslhdsa={path='+json.dumps(str(ROOT/"rust"))+'}\n')
        (p/"Cargo.lock").write_bytes((ROOT/"bench/Cargo.lock").read_bytes())
        (p/"src").mkdir()
        source = ["use slh_dsa::*;"]
        for label, n in sets:
            ty = label.replace("sha2","Sha2").replace("shake_", "Shake")
            source += [f"#[no_mangle] pub fn peer_{label}(k:&[u8;{4*n}])->[u8;{2*n}] {{"
                       f"let sk=SigningKey::<{ty}>::try_from(k.as_slice()).unwrap();"
                       f"let pk:&VerifyingKey<{ty}>=sk.as_ref(); pk.to_bytes().into() }}",
                       f"#[no_mangle] pub fn ours_{label}(k:&[u8;{4*n}])->[u8;{2*n}] {{ slhdsa::{label}::public_key(k) }}"]
        (p/"src/lib.rs").write_text("\n".join(source))
        subprocess.run(["cargo","metadata","--offline","--format-version","1"],cwd=p,stdout=subprocess.DEVNULL,check=True)
        for target in targets:
            dest = p/"build"/target
            subprocess.run(["cargo","rustc","--locked","--release","--lib","--target",target,
                            "--target-dir",str(dest),"--","--emit=llvm-ir"],cwd=p,check=True)
            file, = dest.rglob("relproof*.ll")
            ir = file.read_text()
            for label,n in sets:
                expected = list(range(2*n,4*n))
                for prefix in ("ours","peer"):
                    if origin_map(ir,prefix+"_"+label,n) != expected:
                        raise ValueError(f"wrong output for {target} {prefix} {label}")
            print(f"{target}: all 12 public-key extractions equal on every fixed-size private key", flush=True)


if __name__ == "__main__":
    main()
