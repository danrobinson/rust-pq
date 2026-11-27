#!/usr/bin/env python3
"""Bind active-lane SHAKE short and parent hashes to all hosted Rust targets."""

from pathlib import Path
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
dest = lean / "Cachepath/NativeVerify/ActiveHashProgram.lean"


def program(pkg, width):
    header = """import Cachepath.NativeVerify.Words
import Cachepath.NativeVerify.Active
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ActiveHash
open ShakeBatch
variable [machine : Machine] (permute : Active machine)
"""
    body = []
    for d in decls(pkg / "Funs.lean", "slhdsa"):
        if d.startswith("def shake.batch.") or re.search(
            r"\bdef shake\.batch\.\w+_active", d.partition(":=")[0]
        ):
            d = re.sub(
                r"(Array\.repeat\s+|Std\.U64\s+|address\.Adrs\s+|Std\.U8\s+N\)\s+)"
                + str(width)
                + r"#usize",
                r"\g<1>machine.width",
                d,
            )
            d = (
                d.replace("shake.batch.seed_words", "NativeVerify.seed_words")
                .replace("shake.batch.adrs_words", "NativeVerify.adrs_words")
                .replace("shake.batch.word", "ShakeBatch.shake.batch.word")
                .replace("shake.batch.", "", 1)
            )
            for root in ("header_active", "read_active", "put_active"):
                d = d.replace("shake.batch." + root, root)
            d = d.replace("shake256.parallel.permute_active", "permute")
            body.append(d)
    if len(body) != 21:
        raise ValueError(f"expected 21 active helpers, got {len(body)}")
    return header + "\n\n".join(body) + "\nend slhdsa.NativeVerify.ActiveHash\n"


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    )
    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"]:
            pkg = facade["extract"](
                "rust",
                target,
                "Active",
                Path(tmp),
                ["crate::shake::batch::" + x for x in ("short_active", "pair_active")],
                [
                    "crate::shake::batch::" + x
                    for x in ("word", "seed_words", "adrs_words")
                ]
                + ["crate::shake256"],
                ["crate::shake256::parallel::WIDTH"],
            )
            if (
                program(pkg, 3 if "aarch64-unknown" in target else 8)
                != dest.read_text()
            ):
                raise ValueError(f"{target} active hash program changed")
    module = "Cachepath.NativeVerify.ActiveHashes"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](
        module,
        [
            "slhdsa.NativeVerify.ActiveHash." + n
            for n in ("short_correct", "pair_correct")
        ],
    )


if __name__ == "__main__":
    main()
