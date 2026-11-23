#!/usr/bin/env python3
"""Replay the linked Apple arm64 consumer proofs against one immutable file snapshot."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
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
    parser.add_argument(
        "--require-session-image", action="store_true",
        help="require an exact match to the image-specific end-to-end session witnesses",
    )
    parser.add_argument("--jobs", type=int, default=1, help="number of independent symbolic checks to run concurrently")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    data = args.binary.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env["PATH"]
    subprocess.run(
        [
            "lake",
            "build",
            "Facade.NativeAgreement",
            "Spec.AppleNativeSession",
            "Spec.AppleChainScheduler",
            "Spec.ArmRootComparison",
            "Spec.AppleKeygenWitness",
            "Spec.AppleVerifyLengthWitness",
            "Spec.AppleSha2NativeSession",
            "Spec.AppleSha2PublicVerifyWitness",
            "Spec.ApplePureNativeSession",
            "Spec.ApplePureFrameWitness",
            "Spec.AppleRateBlocksWitness",
            "Spec.AppleSignRejectWitness",
        ],
        cwd=ROOT / "lean",
        env=env,
        check=True,
    )
    subprocess.run(
        ["lake", "build", "Shakebatch.LinkedOrder"],
        cwd=ROOT / "lean-hw", env=env, check=True,
    )
    if args.self_test:
        subprocess.run(
            ["uv", "run", "--python", "3.12", "--script",
             ROOT / "scripts/linked-signer/audit_contracts.py"],
            env=env, cwd=ROOT, check=True,
        )
    with tempfile.TemporaryDirectory() as tmp:
        artifact = Path(tmp) / "consumer"
        artifact.write_bytes(data)
        artifact.chmod(0o444)
        flags = ["--self-test"] if args.self_test else []

        def run(tool, *extra, output=None):
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
            subprocess.run([*cmd, artifact, *extra], env=env, cwd=ROOT, check=True,
                           stdout=output, stderr=subprocess.STDOUT if output else None)

        image_flags = ["--require-session-image"] if args.require_session_image else []
        run("apple-binary/check.py", *flags, *image_flags)
        for name in [
            "apple-binary/check_digest.py",
            "apple-binary/root_compare.py",
            "apple-binary/absorb.py",
        ]:
            run(name, *flags)
        symbolic = [
            ("sha2_chain_scheduler",), ("wots_batch",), ("sha2_fors", "--jobs", "4"),
            ("driver",), ("segmented",), ("keygen",), ("verify",),
            ("sha2_hypertree",), ("sha2_tree_hash",), ("sha2_wots",), ("sha2_chain",),
            ("sha2_fors_sign",), ("sha2_fors_hash",), ("sha2_hash_helpers",),
            ("mgf",), ("wots_digits",), ("xmss_sign",), ("xmss_recover",),
            ("xmss_node",), ("tree_hash",), ("continued", "--jobs", "4"),
            ("sha_from", "--jobs", "4"),
        ]

        def check_symbolic(job):
            name, *extra = job
            path = Path(tmp) / f"{name}.log"
            with path.open("w") as log:
                run(f"linked-signer/{name}.py", *extra, *flags, output=log)

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            submitted = {pool.submit(check_symbolic, job): job[0] for job in symbolic}
            for future in as_completed(submitted):
                log = Path(tmp) / f"{submitted[future]}.log"
                print(log.read_text(), end="", flush=True)
                future.result()
        run("linked-signer/fors.py")
        if args.self_test:
            run("linked-signer/fors.py", "--mutations")
        if artifact.read_bytes() != data:
            raise RuntimeError("consumer snapshot changed during verification")
    print(f"All requested checks passed for Mach-O SHA-256 {digest}", flush=True)


if __name__ == "__main__":
    main()
