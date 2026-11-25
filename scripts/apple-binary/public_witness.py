"""Regenerate and kernel-check public driver claims against a supplied linked image."""

import argparse
import os
from pathlib import Path
import subprocess

from check import release_consumer
from image import Image


def check_witness(description, extract, recorded, modules):
    p = argparse.ArgumentParser(description=description)
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
    program, names = extract(Image((args.binary or release_consumer()).read_bytes()))
    if args.require_recorded and program != recorded.read_text():
        raise ValueError(f"the supplied consumer differs from {recorded.name}")
    subprocess.run(
        ["lake", "build", *modules],
        cwd=recorded.parents[1],
        check=True,
    )
    audit = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=recorded.parents[1],
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
                "depends on axioms: [propext, Quot.sound]",
                "depends on axioms: [propext]",
                "does not depend on any axioms",
            )
        ):
            raise ValueError(f"unexpected axiom audit for {name}: {audit.stdout}")
