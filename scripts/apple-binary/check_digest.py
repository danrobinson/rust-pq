#!/usr/bin/env python3
"""Bind the linked H_msg drivers and single-rate-block SHAKE finalizer to their Lean summaries.

Sponge::absorb must implement incremental Keccak absorption and preserve the ABI.
Assumes valid input regions, a disjoint stack/output, and successful allocation.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import re

import finish
import hmsg
import single
from check import certificate, release_consumer, ROOT
from image import Image, require
from permute import decode


SETS = {16: [30, 34], 24: [39, 42], 32: [47, 49]}


def check(image):
    address, lanes, table, instructions, layout = decode(image)
    single.verify(image, address)
    witness = (ROOT / "lean/Spec/AppleKeccakWitness.lean").read_text().split("\n", 1)[1]
    require(
        witness == certificate(lanes, table, instructions, layout),
        "different Keccak witness",
    )
    addr, size = finish.verify(image)
    sites = dict(finish=dict(entry=hex(addr), size=size))
    for width, lengths in SETS.items():
        for n in lengths:
            addr, size = hmsg.verify(image, width, n)
        sites[f"H_msg_{width * 8}"] = dict(
            entry=hex(addr), size=size, digest_lengths=lengths
        )
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env["PATH"]
    subprocess.run(
        ["lake", "build", "Spec.AppleShakeDigest"],
        cwd=ROOT / "lean",
        env=env,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    audit = "import Spec.AppleShakeDigest\n"
    for w, lengths in SETS.items():
        for style, n in zip(("s", "f"), lengths):
            p = f"Spec.shake_{w * 8}{style}"
            audit += f"example : {p}.n = {w} ∧ {p}.m = {n} ∧ {p}.family = .shake := by decide\n"
    theorems = ["LinkedArm.Digest.finish_eq", "LinkedArm.Digest.hmsg_eq"]
    audit += "".join(f"#print axioms {t}\n" for t in theorems)
    report = subprocess.check_output(
        ["lake", "env", "lean", "--stdin"],
        input=audit,
        text=True,
        cwd=ROOT / "lean",
        env=env,
    )
    for name in theorems:
        (axioms,) = re.findall(
            r"^'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", report, re.M
        )
        require(
            set(map(str.strip, axioms.split(",")))
            <= {"propext", "Classical.choice", "Quot.sound"},
            "unexpected axioms",
        )
    return dict(
        artifact_sha256=hashlib.sha256(image.data).hexdigest(),
        functions=sites,
        theorems=theorems,
    )


def controls(image):
    def mutated(addr, mask):
        raw = bytearray(image.data)
        index = addr - image.base
        (word,) = struct.unpack_from("<I", raw, index)
        struct.pack_into("<I", raw, index, word ^ mask)
        return Image(raw)

    pc, _ = finish.verify(image)
    hp, _ = hmsg.verify(image, 16, 30)
    for addr, mask, checker, message in [
        (pc + 0x30, 1 << 5, finish.verify, "wrong SHAKE domain"),
        (pc + 0x54, 1, finish.verify, "wrong finish permutation"),
        (pc + 0x80, 1 << 5, finish.verify, "unsupported finish output"),
        (hp + 0x64, 1 << 16, lambda i: hmsg.verify(i, 16, 30), "wrong absorption"),
        (hp + 0xF4, 1, lambda i: hmsg.verify(i, 16, 30), "wrong sponge"),
        (
            hp + 0x118,
            1 << 10,
            lambda i: hmsg.verify(i, 16, 30),
            "incorrect result pointer",
        ),
    ]:
        try:
            checker(mutated(addr, mask))
        except ValueError as err:
            require(message in str(err), f"unexpected rejection: {err}")
        else:
            raise ValueError("mutated digest passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, nargs="?")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    image = Image((args.binary or release_consumer()).read_bytes())
    result = check(image)
    if args.self_test:
        controls(image)
        result["rejected_mutations"] = 6
    print(json.dumps(result, indent=2))
