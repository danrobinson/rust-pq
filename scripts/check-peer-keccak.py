#!/usr/bin/env python3
"""Reextract and verify the benchmark-locked RustCrypto Keccak-f[1600] kernels."""
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

locked = runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))
ROOT = locked["ROOT"]
LEAN = ROOT / "lean-hw"
PACKAGE = LEAN / "Peerarmkeccak"
ARM = ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu")


def arm_source(path, manifest, target):
    scratch = path / target
    scratch.mkdir()
    file = scratch / "peerarmkeccak.llbc"
    subprocess.run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
                    "--start-from", "crate::backends::aarch64_sha3::p1600_armv8_sha3",
                    "--dest-file", file, "--", "--locked", "--manifest-path", manifest,
                    "--target", target, "--target-dir", path / "target"], cwd=path, check=True)
    subprocess.run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
                    "-no-progress-bar", "-namespace", "PeerArmRust", "-split-files",
                    "-dest", scratch, file], cwd=path, check=True)
    for name in ("Funs.lean", "Types.lean"):
        if (scratch / name).read_bytes() != (PACKAGE / name).read_bytes():
            raise ValueError(f"{target} pinned Keccak source diverges in {name}")


def audit(path, modules, names):
    subprocess.run(["lake", "build", *modules], cwd=LEAN, check=True)
    f = path / "Check.lean"
    f.write_text("".join(f"import {mod}\n" for mod in modules)
                 + "".join(f"#print axioms {name}\n" for name in names))
    output = subprocess.check_output(["lake", "env", "lean", f], cwd=LEAN, text=True)
    for name in names:
        line, = [line for line in output.splitlines() if f"'{name}'" in line]
        match = re.search(r"depends on axioms: \[(.*?)\]", line)
        if not match or set(match[1].split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError(line)


def main():
    os.environ["PATH"] = os.pathsep.join(str(Path.home() / t / "bin") for t in (".elan", ".cargo")) + os.pathsep + os.environ["PATH"]
    with tempfile.TemporaryDirectory(prefix="peer-keccak-") as d:
        root = Path(d)
        manifest = locked["unpack"](root, "keccak", "0.2.2")
        for target in ARM:
            arm_source(root, manifest, target)
        audit(root, ["Peerarmkeccak.Top"], ["PeerKeccak.Arm.both", "PeerKeccak.Arm.single"])


if __name__ == "__main__":
    main()
