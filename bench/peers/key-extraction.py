#!/usr/bin/env python3
"""Revisit the short public-key copies using the archived pairs and benchmark code."""
import argparse
import csv
import gzip
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "bench/results/peers-optimized"
TARGETS = ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"]


def samples():
    with (DATA / "workloads.csv").open() as stream:
        misses = [r for r in csv.DictReader(stream)
                  if r["operation"] == "public_key" and float(r["rustcrypto_over_library_median"]) <= 1]
    with gzip.open(DATA / "raw-key-samples.csv.gz", "rt") as stream:
        paired = [r for r in csv.DictReader(stream) if r["operation"] == "public_key" and int(r["round"]) > 0]
    for cpu, name in sorted({(r["cpu"], r["set"]) for r in misses}):
        rounds = [r for r in paired if (r["cpu"], r["set"]) == (cpu, name)]
        if sorted(int(r["round"]) for r in rounds) != list(range(1, 21)):
            raise ValueError(f"incomplete focused pairs for {cpu}/{name}")
        deltas = sorted(float(r["rustcrypto_ns"]) - float(r["library_ns"]) for r in rounds)
        print(f"{cpu} {name}: library {median(float(r['library_ns']) for r in rounds):.4f} ns,"
              f" RustCrypto {median(float(r['rustcrypto_ns']) for r in rounds):.4f} ns,"
              f" paired difference {median(deltas):.4f} ns [{deltas[5]:.4f}, {deltas[14]:.4f}],"
              f" library faster in {sum(d > 0 for d in deltas)}/{len(deltas)} pairs")


def assembly(target, cpu):
    """Compile the full primary matrix. Its first four extraction loops are SHA2-128s/f."""
    with tempfile.TemporaryDirectory(prefix="slh-key-copy-") as tmp:
        work = Path(tmp)
        source = (ROOT / "bench/peers/public.rs").read_text()
        if source.count("fn main() {") != 1:
            raise ValueError("unexpected driver entry")
        src = source.replace("fn main() {", '#[unsafe(export_name = "matrix_main")] pub fn main() {')
        (work / "public.rs").write_text(src)
        (work / "Cargo.toml").write_text(f"""
[package]
name = "slh-key-matrix"
version = "0.1.0"
edition = "2021"
[dependencies]
slhdsa = {{ path = "{ROOT / 'rust'}", features = ["platform-sha2"] }}
upstream = {{ package = "slh-dsa", version = "=0.2.0-rc.5" }}
[lib]
path = "public.rs"
[workspace]
""")
        shutil.copy2(ROOT / "rust/Cargo.lock", work / "Cargo.lock")
        cmd = ["cargo", "rustc", "--offline", "--release", "--target", target, "--target-dir", str(work / "target"), "--lib", "--",
               "--emit=asm"]
        if cpu:
            cmd.append("-Ctarget-cpu=" + cpu)
        # Only metadata for the temporary crate changes in the existing dependency lock.
        subprocess.run(cmd, cwd=work, check=True)
        built, = (work / "target" / target / "release").rglob("slh_key_matrix*.s")
        lines = built.read_text().splitlines()
        start = lines.index("matrix_main:")
        if target.startswith("x86_64"):
            count = re.compile(r"\s*movl\s+\$255,")
        else:
            count = re.compile(r"\s*mov\s+w\d+, #255$")
        starts = [i for i in range(start, len(lines)) if count.match(lines[i])]
        if len(starts) != 24:
            raise ValueError(f"expected 24 public_key measurement loops, found {len(starts)}")
        for i, name in zip(starts, ["RustCrypto SHA2-128s", "library SHA2-128s",
                                   "RustCrypto SHA2-128f", "library SHA2-128f"]):
            print(name)
            begin = next(j for j in range(i, i + 80) if lines[j].startswith(".LBB"))
            label = lines[begin].strip().rstrip(":")
            end = next(j for j in range(begin + 1, begin + 130)
                       if re.fullmatch(r"\s*(?:jne|b\.ne)\s+" + re.escape(label), lines[j]))
            for line in lines[begin:end + 1]:
                if re.match(r"\s*[a-z]", line):
                    print(line)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assembly", choices=TARGETS, help="emit the actual primary measurement loops")
    parser.add_argument("--cpu", help="optional rustc target CPU for assembly comparison")
    args = parser.parse_args()
    if args.assembly:
        assembly(args.assembly, args.cpu)
    else:
        samples()
