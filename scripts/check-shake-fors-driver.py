#!/usr/bin/env python3
"""Bind the complete eight-lane FORS signature driver on Apple and x86."""
import os
from pathlib import Path
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-shake-fors-scatter.py")))
facade, lean = shared["facade"], shared["lean"]
dest = lean / "ForsDriver/Program.lean"
header = """import Cachepath.NativeVerify.ForsWideRowsProgram
import Cachepath.NativeVerify.ForsSignNarrow
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance driverMachine : Machine := Fused.machine kernel
class Trees where
  node {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)
  fallback {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Array U32 8#usize → U32 → Usize → Result (Array (Array U8 N) 8#usize)
variable [trees : Trees]
"""


def program(pkg):
    calls = (pkg / "Funs.lean").read_text()
    if "def shake256.parallel.WIDTH : Std.Usize := 8#usize" not in calls:
        raise ValueError("expected the native eight-lane constant")
    source = calls[calls.index("def shake.fors_batch.sign_loop2.body"):calls.rindex("end slhdsa")]
    source = re.sub(r"/--[\s\S]*?-/", "", source)
    for old, new in {
        "shake.fors_batch.sign_loop0 selections": "ForsSign.sign_loop0 (ActiveHash.short_active kernel.active) selections",
        "shake.fors_batch.sign_loop1 iter": "ForsSign.sign_loop1 trees.fallback iter",
        "shake.fors_batch.sign": "sign",
        "shake256.parallel.WIDTH": "8#usize",
        "shake.fors_batch.fors_subtree_horiz": "trees.node",
        "shake.fors_batch.batch_leaves_slice": "ForsWideRows.leaves",
        "shake.fors_batch.batch_pairs_slice": "ForsWideRows.pairs",
    }.items():
        source = source.replace(old, new)
    return header + "\n@[rust_loop_body]\n" + source.strip() + "\nend slhdsa.ForsDriver\n"


def main():
    runpy.run_path(str(Path(__file__).with_name("check-fors-wide-rows.py")))["main"]()
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    module = "ForsDriver.Entry"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](module, ["slhdsa.ForsDriver." + name for name in (
        "sign_spec", "raw_eq", "prepare_spec", "Fields.store", "column1", "column2",
        "column3", "level_zero", "level_one", "level_two", "sibling_local",
        "low0_spec", "low1_spec", "low2_spec", "upper")])
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            folder = Path(tmp) / target
            folder.mkdir()
            pkg = facade["extract"]("rust", target, "Unsigned", folder, ["crate::shake::fors_batch::sign"],
                                    shared["cuts"], ["crate::shake256::parallel::WIDTH"])
            if program(pkg).split() != dest.read_text().split():
                raise ValueError(f"FORS signature driver differs on {target}")
            original = (pkg / "Funs.lean").read_text()
            # A changed authentication-field offset must break the source binding.
            changed = original.replace("let i1 ← 2#usize * N", "let i1 ← 3#usize * N", 1)
            mutant = folder / "wrong-offset"
            mutant.mkdir()
            (mutant / "Funs.lean").write_text(changed)
            if program(mutant).split() == dest.read_text().split():
                raise ValueError(f"changed authentication field escaped detection on {target}")
            base = lean / "Cachepath/NativeVerify"
            if shared["program"](pkg, 8) != (base / "ForsSignScatterProgram.lean").read_text():
                raise ValueError(f"FORS secret loop differs on {target}")
            if shared["fallback_program"](pkg, 8) != (base / "ForsSignAuthProgram.lean").read_text():
                raise ValueError(f"FORS fallback differs on {target}")


if __name__ == "__main__":
    main()
