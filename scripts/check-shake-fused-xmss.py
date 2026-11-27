#!/usr/bin/env python3
"""Check the width-eight signing kernel's selected chain value and every returned authentication tree."""

import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
from keygen_subtrees import program

facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
table = facade["LEAN"] / "Parallel/FusedShapeTable.lean"


def check(folder):
    source = (HERE.parent / "rust/src/shake/batch.rs").read_text()
    if program(folder, source, signing=True) != table.read_text():
        raise ValueError("XMSS authentication store or subtree changed")
    bad_capture = "if step + 1 == d {"
    if source.count(bad_capture) != 1:
        raise ValueError("missing fused capture")
    try:
        program(folder, source.replace(bad_capture, "if step == d {"), signing=True)
    except ValueError as err:
        if "fused SHAKE signer binding" not in str(err):
            raise
    else:
        raise ValueError("accepted a wrong WOTS capture")
    old = "let auth2 = thash_pair(seed, &a2, &lvl1[1], &lvl1[2]);"
    if source.count(old) != 1:
        raise ValueError("missing level-two merge")
    bad = program(
        folder,
        source.replace(old, old.replace("&lvl1[1], &lvl1[2]", "&lvl1[2], &lvl1[1]")),
        signing=True,
    )
    if bad == table.read_text():
        raise ValueError("swapped siblings yielded the same dependency tree")
    # Elaborate the soundness theorem against the mutated source's shape table.
    proof = (table.parent / "FusedSignature.lean").read_text()
    probe = proof.replace(
        "import Parallel.FusedShapeTable", "import Parallel.KeygenShape"
    )
    header, body = probe.split("namespace ParallelFusedSignature", 1)
    probe = (
        header
        + bad.split("import Parallel.KeygenShape", 1)[1]
        + "\nnamespace ParallelFusedSignature"
        + body
    )
    rejected = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=facade["LEAN"],
        input=probe,
        text=True,
        stdout=subprocess.PIPE,
    )
    if rejected.returncode == 0 or "decide" not in rejected.stdout:
        raise ValueError("expected Lean to reject the mutated level-two certificate")


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    )
    with tempfile.TemporaryDirectory() as tmp:
        check(Path(tmp))
    module = "Parallel.FusedSignature"
    facade["run"](["lake", "build", module], facade["LEAN"])
    facade["audit_theorems"](module, ["ParallelFusedSignature.sign_fips"])
    src = [f"import {module}", "open Spec ParallelFusedSignature"]
    for n in (128, 192, 256):
        for mode in "sf":
            p = f"shake_{n}{mode}"
            src.append(
                f"example (m sk pk : Bytes) (i : Nat) (a : Adrs) (initial : Nat → Bytes) : sign {p} m sk i pk a initial = xmssSign {p} m sk i pk a := sign_fips {p} m sk i pk a initial (by decide) (by decide) (by decide)"
            )
    facade["run"](
        ["lake", "env", "lean", "--stdin"],
        facade["LEAN"],
        input="\n".join(src),
        text=True,
    )
    print(
        "Verified the fused signer for all six SHAKE sets; rejected shifted WOTS capture and swapped XMSS children."
    )


if __name__ == "__main__":
    main()
