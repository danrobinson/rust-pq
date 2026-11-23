#!/usr/bin/env python3
"""Replay the linked Apple arm64 consumer proofs against one immutable file snapshot."""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="also run instruction mutation controls",
    )
    args = parser.parse_args()
    data = args.binary.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env["PATH"]
    with tempfile.TemporaryDirectory() as tmp:
        artifact = Path(tmp) / "consumer"
        artifact.write_bytes(data)
        artifact.chmod(0o444)
        flags = ["--self-test"] if args.self_test else []

        def run(tool, *extra):
            print(f"Checking {tool} against {digest}", flush=True)
            script = ROOT / "scripts" / tool
            if tool.startswith("linked-signer/"):
                cmd = ["uv", "run", "--python", "3.12", "--script", script]
            elif tool.endswith("/absorb.py"):
                cmd = [
                    "uv",
                    "run",
                    "--python",
                    "3.12",
                    "--with",
                    "z3-solver==4.15.4.0",
                    "python",
                    script,
                ]
            else:
                cmd = [sys.executable, script]
            subprocess.run([*cmd, artifact, *extra], env=env, cwd=ROOT, check=True)

        for name in [
            "apple-binary/check.py",
            "apple-binary/check_digest.py",
            "apple-binary/absorb.py",
        ]:
            run(name, *flags)
        for name in [
            "driver",
            "segmented",
            "keygen",
            "verify",
            "sha2_hypertree",
            "sha2_tree_hash",
            "wots_digits",
            "xmss_sign",
            "xmss_recover",
            "xmss_node",
            "tree_hash",
        ]:
            run(f"linked-signer/{name}.py", *flags)
        run("linked-signer/fors.py")
        if args.self_test:
            run("linked-signer/fors.py", "--mutations")
        if artifact.read_bytes() != data:
            raise RuntimeError("consumer snapshot changed during verification")
    print(f"All requested checks passed for Mach-O SHA-256 {digest}", flush=True)


if __name__ == "__main__":
    main()
