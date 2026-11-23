"""Negative control for Rust-to-Lean hash input ordering.

Swap the two H updates after archive validation, retranslate both security
categories, and require the unmodified FIPS theorem to fail on all six sets.
Temporary artifacts shadow only the generated suite in Lean's search path.
"""

import importlib.util
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent.parent
    project = root / "lean-hw"
    descriptor = importlib.util.spec_from_file_location(
        "suite", root / "scripts/extract-peer-sha2-suite.py"
    )
    suite = importlib.util.module_from_spec(descriptor)
    descriptor.loader.exec_module(suite)
    original = suite.translate

    def swapped(level, source):
        changed, count = re.subn(
            r"\.chain_update\(m1\)(\s*)\.chain_update\(m2\)",
            r".chain_update(m2)\1.chain_update(m1)",
            source,
        )
        if count != 1:
            raise ValueError(
                "negative control could not identify the two H input updates"
            )
        return original(level, changed)

    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        package = tmp / "RcSlhSha2"
        package.mkdir()
        (tmp / "lean-toolchain").write_bytes((project / "lean-toolchain").read_bytes())
        for artifact in (project / ".lake/build/lib/lean/RcSlhSha2").iterdir():
            if artifact.name.partition(".")[0] not in ("Suite", "Proof"):
                (package / artifact.name).symlink_to(artifact)

        suite.translate = swapped
        sys.argv = ["extract", str(package / "Suite.lean"), str(tmp / "Initial.lean")]
        suite.main()
        if (package / "Suite.lean").read_bytes() == (
            project / "RcSlhSha2/Suite.lean"
        ).read_bytes():
            raise ValueError("reordered Rust generated an identical suite")
        (package / "Proof.lean").write_bytes(
            (project / "RcSlhSha2/Proof.lean").read_bytes()
        )
        paths = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True
        ).strip()
        env = os.environ | {
            "LEAN_PATH": os.pathsep.join(
                [
                    str(tmp),
                    *(str((project / p).resolve()) for p in paths.split(os.pathsep)),
                ]
            )
        }
        subprocess.run(
            ["lean", "-o", "RcSlhSha2/Suite.olean", "RcSlhSha2/Suite.lean"],
            cwd=tmp,
            env=env,
            check=True,
        )
        failure = subprocess.run(
            ["lean", "RcSlhSha2/Proof.lean"],
            cwd=tmp,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )
        cases = ("s128", "f128", "s192", "f192", "s256", "f256")
        if not (
            failure.returncode
            and "unsolved goals" in failure.stdout
            and all("case " + case in failure.stdout for case in cases)
        ):
            raise RuntimeError(
                "expected a failed FIPS theorem in each set\n"
                + failure.stdout
                + failure.stderr
            )
        print(
            "Reversing the two Rust H inputs is rejected for all six SHA-2 parameter sets."
        )


if __name__ == "__main__":
    main()
