#!/usr/bin/env python3
"""Kernel-check the Apple parallel key-generation driver for both possible worker returns."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from current_keygen import page, sha256_seed
from image import Image, require, sign_extend

ROOT = Path(__file__).resolve().parents[2]


def candidate(image, entry, worker, root, external, inline, used):
    pc, links, words, tag = entry, [], [], False
    for _ in range(512):
        if pc == worker:
            pc, tag = links.pop(), True
        elif pc in (root, external):
            pc = links.pop()
        if inline and pc == inline[0]:
            pc += 4 * len(inline[1])
        w = int.from_bytes(image.read(b"__text", pc, 4), "little")
        words.append((pc, w))
        if w == 0xD65F03C0:
            if not links:
                return words
            pc = links.pop()
        elif w >> 26 in (5, 37):
            if w >> 26 == 37:
                links.append(pc + 4)
            pc += 4 * sign_extend(w % (1 << 26), 26)
        elif w & 0xFF000000 == 0x34000000:
            pc += 4 * sign_extend((w >> 5) % 2**19, 19) if tag and not used else 4
            tag = False
        elif w & 0xFF00001F == 0x54000008:
            pc += 4 * sign_extend((w >> 5) % 2**19, 19)
        else:
            pc += 4
    raise ValueError("no bounded key-generation return in this candidate")


def witness(image):
    out = [
        "import Spec.ArmParallelKeygen",
        "open Spec.ArmKeygen Spec.ArmParallelKeygen",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    names = []
    for family in ("shake", "sha2"):
        shake = family == "shake"
        for n in (16, 24, 32):
            suffix = f"Kj{n:x}_EB{6 if shake else 4}_".encode()
            crate = b"6slhdsa5shake" if shake else b"6slhdsa"
            root, _ = image.function(
                (b"5batch12xmss_subtree" if shake else b"4xmss9xmss_node") + suffix,
                crate,
            )
            worker, _ = image.function(
                b"3slh8parallel6keygen" + f"Kj{n:x}_EB{8 if shake else 6}_".encode(),
                crate,
            )
            ext = inline = None
            seed = ".shake"
            if not shake and n == 16:
                inline, decl = sha256_seed(image, suffix)
                out.append(decl)
                seed = "seed128"
            elif not shake:
                ext, _ = image.function(b"4hash8seed_ctx" + suffix, crate)
                seed = f".external 0x{ext:x}"
            for shape in "sf":
                suite = f"{family}_{8 * n}{shape}"
                for op in ("keygen", "slh_keygen_internal"):
                    entry, _ = image.function(
                        f"{len(suite)}{suite}{len(op)}{op}".encode(), b"6slhdsa4sets"
                    )
                    for used in (False, True):
                        name = f"{suite}_{op}_{'some' if used else 'none'}"
                        steps = candidate(image, entry, worker, root, ext, inline, used)
                        (param,) = [
                            page(pc, w) + (v >> 10 & 4095)
                            for (pc, w), (_, v) in zip(steps, steps[1:])
                            if w & 0x9F00001F == 0x90000000
                            and v & 0xFFC003FF == 0x91000000
                        ]
                        const = list(image.read(b"__const", param, 36))
                        trace = ", ".join(f"(0x{a:x},0x{w:x})" for a, w in steps)
                        p = f"Spec.{suite}"
                        config = name + "_cfg"
                        out.extend(
                            [
                                f"def {config} : Config := ⟨{n},{p}.d,{p}.hp,{entry},{root},{param},{const},{str(op != 'keygen').lower()},{seed}⟩",
                                f"example : {config}.params=parameterBytes {p} := by decide",
                                f"def {name}_ops : List (Nat × Nat) := [{trace}]",
                            ]
                        )
                        args = f"{config} {worker} {str(used).lower()} {name}_ops"
                        out.extend(
                            [
                                f"theorem {name}_trace : Spec.ArmParallelKeygen.run {args}=some (secret {n}, publicKey {n}) := by decide +kernel",
                                f"theorem {name}_fips (s r k : Spec.Bytes) (hs : s.length={n}) (hr : r.length={n}) (hk : k.length={n}) : "
                                + f"(Spec.ArmParallelKeygen.run {args}).map (fun keys => let f := interpret (Spec.ArmPublicKeygen.inputs {p} s r k); "
                                + f"(bytes f keys.1, bytes f keys.2))=some (Spec.slhKeygenInternal {p} s r k) := "
                                + f"Spec.ArmParallelKeygen.fips {p} (by constructor <;> decide) {args} {name}_trace (by decide) (by decide) s r k hs hr hk",
                            ]
                        )
                        names.append(name + "_fips")
                        if used and shape == "s" and op == "keygen":
                            out.append(
                                f"example : Spec.ArmParallelKeygen.run {config} {worker} false {name}_ops = none := by decide +kernel"
                            )
                        if name == "shake_128s_keygen_some":
                            (tag_pc,) = [
                                pc + 4
                                for pc, w in steps
                                if w >> 26 == 37
                                and pc + 4 * sign_extend(w % (1 << 26), 26) == worker
                            ]
                            out.extend(
                                [
                                    f"def wrongTag := {name}_ops.map (fun (pc,w) => (pc, if pc=={tag_pc} then w ^^^ 1024 else w))",
                                    f"example : Spec.ArmParallelKeygen.run {config} {worker} true wrongTag = none := by decide +kernel",
                                    f"example : Spec.ArmParallelKeygen.run {config} {worker + 4} true {name}_ops = none := by decide +kernel",
                                ]
                            )
    return "\n".join(out), names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, nargs="?")
    args = parser.parse_args()
    os.environ["PATH"] = (
        f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    )
    binary = args.binary
    if binary is None:
        output = subprocess.check_output(
            [
                "cargo",
                "test",
                "--release",
                "--locked",
                "--features",
                "parallel",
                "--test",
                "acvp",
                "--no-run",
                "--message-format=json",
            ],
            cwd=ROOT / "rust",
            text=True,
        )
        (binary,) = [
            Path(m["executable"])
            for line in output.splitlines()
            if (m := json.loads(line)).get("executable")
            and m["target"]["name"] == "acvp"
        ]
    image = Image(binary.read_bytes())
    code, names = witness(image)
    lean = ROOT / "lean"
    subprocess.run(["lake", "build", "Spec.ArmParallelKeygen"], cwd=lean, check=True)
    r = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=code + "\n" + "\n".join("#print axioms " + n for n in names),
        cwd=lean,
        text=True,
        capture_output=True,
    )
    if r.returncode:
        raise ValueError(r.stdout + r.stderr)
    for name in names:
        match = re.findall(
            rf"^'{name}' depends on axioms: \[([^\]]+)\]$", r.stdout, re.M
        )
        require(
            len(match) == 1
            and set(match[0].split(", "))
            <= {"propext", "Classical.choice", "Quot.sound"},
            "unexpected axiom closure",
        )
    # Reuse the exact bytes for the independent instruction-level seed proof.
    with tempfile.TemporaryDirectory() as directory:
        snapshot = Path(directory) / "parallel-acvp"
        snapshot.write_bytes(image.data)
        subprocess.run(
            [
                "uv",
                "run",
                "--script",
                ROOT / "scripts/linked-signer/parallel_seed.py",
                snapshot,
            ],
            check=True,
        )
    print(
        f"Checked both parallel worker returns for all 24 public keygen entries in {hashlib.sha256(image.data).hexdigest()}."
    )


if __name__ == "__main__":
    main()
