#!/usr/bin/env python3
"""Bind all oversize-context signing returns to an Apple arm64 release consumer."""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from check import release_consumer
from image import Image
from reject import candidate, unwrap_abi
from sha2_verify_witness import gate as sha2_length
from verify_length_witness import certificate as shake_length

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "lean/Spec/ApplePublicRejectWitness.lean"


def certificate(image):
    unwrap_abi(image)
    sha = hashlib.sha256(image.data).hexdigest()
    lines = [
        "import Spec.ArmPublicReject",
        "namespace LinkedPublicReject",
        "open Spec.ArmPublicReject",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        f"-- Mach-O SHA-256 {sha}",
    ]
    names = []
    for family in ("sha2", "shake"):
        for n in (16, 24, 32):
            for shape in "sf":
                suite = f"{family}_{8 * n}{shape}"
                for op in ("sign", "slh_sign", "sign_deterministic"):
                    symbol = f"{len(suite)}{suite}{len(op)}{op}".encode()
                    entry, _ = image.function(symbol, b"6slhdsa4sets")
                    path = candidate(image, entry)
                    name = f"{suite}_{op}"
                    rows = ", ".join(f"(0x{pc:x},0x{w:08x})" for pc, w in path)
                    lines.append(f"def {name} := [{rows}]")
                    det = str(op == "sign_deterministic").lower()
                    args = f"0x{entry:x} {n} {det} {name}"
                    lines.append(
                        f"theorem {name}_returns_none : ReturnsNone {args} := returnsNone_of_checks (by decide)"
                    )
                    names.append(f"LinkedPublicReject.{name}_returns_none")
                    if (suite, op) == ("shake_128f", "sign_deterministic"):
                        for label, match, bit in (
                            (
                                "threshold",
                                lambda w: (
                                    w & 0xFFC0001F == 0xF100001F
                                    and (w >> 10) & 4095 == 255
                                ),
                                1 << 10,
                            ),
                            (
                                "return_slot",
                                lambda w: (
                                    w & 0xFFC00000 == 0xF9000000 and (w >> 5) & 31 != 31
                                ),
                                1 << 10,
                            ),
                            (
                                "return_address",
                                lambda w: (
                                    w & 0xFFC003FF == 0xA94003FD
                                    and (w >> 10) & 31 == 30
                                ),
                                1 << 10,
                            ),
                            (
                                "secret_key_offset",
                                lambda w: w & 0xFFC00000 == 0x3DC00000,
                                1 << 10,
                            ),
                        ):
                            matches = [(pc, w) for pc, w in path if match(w)]
                            if not matches or (
                                label != "return_address" and len(matches) != 1
                            ):
                                raise ValueError(
                                    f"ambiguous {label} mutation in {name}"
                                )
                            pc, w = matches[0]
                            mutant = f"({name}.map (fun (pc,w) => (pc,if pc=0x{pc:x} then 0x{w ^ bit:08x} else w)))"
                            lines.append(
                                f"theorem wrong_{label} : checks 0x{entry:x} {n} {det} {mutant} = false := by decide"
                            )
    lines.append("end LinkedPublicReject")
    for family, extractor, old in (
        ("sha2", sha2_length, "LinkedAppleSha2VerifyLength"),
        ("shake", shake_length, "LinkedAppleVerifyLength"),
    ):
        scope = "Current" + old
        fragment = (
            extractor(image)
            .removeprefix("import Spec.ArmVerifyLength\n")
            .replace(old, scope)
        )
        lines.append(fragment)
        for n in (128, 192, 256):
            for shape in "sf":
                names += [
                    f"{scope}.{family}_{n}{shape}_{op}"
                    for op in ("malformed", "hashCall")
                ]
    lines.insert(1, "import Spec.ArmVerifyLength")
    return "\n".join(lines + [""]), names


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "binary",
        nargs="?",
        type=Path,
        help="default: locked platform-sha2 release ACVP consumer",
    )
    p.add_argument(
        "--require-recorded",
        action="store_true",
        help="also match the recorded image and witness verbatim",
    )
    args = p.parse_args()
    os.environ["PATH"] = (
        f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    )
    program, names = certificate(
        Image((args.binary or release_consumer()).read_bytes())
    )
    if args.require_recorded and program != DEST.read_text():
        raise ValueError(
            "the supplied consumer differs from the recorded Apple public rejection witness"
        )
    subprocess.run(
        ["lake", "build", "Spec.ArmPublicReject", "Spec.ArmVerifyLength"],
        cwd=ROOT / "lean",
        check=True,
    )
    audit = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT / "lean",
        text=True,
        input=program + "\n".join(f"#print axioms {n}" for n in names),
        capture_output=True,
    )
    if audit.returncode:
        raise RuntimeError(audit.stdout + audit.stderr)
    closure = " ".join(audit.stdout.split())
    for name in names:
        if not any(
            f"'{name}' {allowed}" in closure
            for allowed in (
                "depends on axioms: [propext, Classical.choice, Quot.sound]",
                "depends on axioms: [propext]",
                "does not depend on any axioms",
            )
        ):
            raise ValueError(f"unexpected axiom audit for {name}: {audit.stdout}")
    print(
        "Kernel checked 36 signing rejections, 12 verifier length guards and their valid paths to H_msg, "
        "with instruction mutations."
    )


if __name__ == "__main__":
    main()
