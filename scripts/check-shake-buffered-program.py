#!/usr/bin/env python3
"""Extract the width-eight SHAKE subtree with explicit snapshots of its read-only rows."""
from pathlib import Path
import os
import re
import runpy
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
from buffered_lift import lift_rows

shared = runpy.run_path(str(HERE / "check-cache-construction.py"))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
root = lean.parent
dest = lean / "Buffered/Program.lean"
callbacks = ("pair_active", "wots_leaves_batch", "wots_leaves_small", "xmss_subtree_fallback")
cuts = ["crate::shake::batch::" + n for n in callbacks] + ["crate::shake::hash::thash_pair", "crate::shake256"]


def program(package):
    prefix = """import Cachepath.NativeVerify.ActiveHashes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Buffered
open ShakeBatch NativeVerify

abbrev Rows8 (N : Usize) := Array (Array U8 N) 8#usize
abbrev Row16 (N : Usize) := Array (Array U8 N) 16#usize
class Kernel where
  active : Matrix 8#usize → Usize → Result (Matrix 8#usize)
  leaves {N : Usize} : Array U8 N → Array U8 N → U32 → address.Adrs → Result (Rows8 N)
  small {N : Usize} (K : Usize) : Array U8 N → Array U8 N → U32 → address.Adrs → Result (Array (Array U8 N) K)
  fallback {N : Usize} : Array U8 N → Array U8 N → U32 → U32 → address.Adrs → Result (Array U8 N)

def machine (k : Kernel) : Machine := ⟨8#usize, fun s => k.active s 8#usize⟩
variable [kernel : Kernel]
local instance bufferedMachine : Machine := machine kernel
"""
    out = []
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    for body in decls(package / "Funs.lean", "slhdsa"):
        if not re.search(r"\bdef shake\.batch\.xmss_subtree(?:_loop\w*)?(?:\.body)?\s", body):
            if body not in known:
                raise ValueError("unrecognized subtree dependency: " + body)
            continue
        for old, new in (("shake.batch.xmss_subtree_fallback", "kernel.fallback"),
                         ("shake.batch.xmss_subtree", "subtree"),
                         ("shake.batch.wots_leaves_batch", "kernel.leaves"),
                         ("shake.batch.wots_leaves_small", "kernel.small"),
                         ("shake.batch.pair_active", "(NativeVerify.ActiveHash.pair_active kernel.active)"),
                         ("shake256.parallel.WIDTH", "(ok 8#usize : Result Usize)")):
            body = body.replace(old, new)
        out.append(body)
    if len(out) != 15:
        raise ValueError(f"expected 15 subtree declarations, got {len(out)}")
    externals = set(re.findall(r"^axiom ([\w.]+)", (package / "FunsExternal_Template.lean").read_text(), re.M))
    if externals != {"shake.batch." + n for n in callbacks} | {"shake.hash.thash_pair", "shake256.parallel.WIDTH"}:
        raise ValueError("unexpected buffered subtree cutpoints " + str(externals))
    if not set(decls(package / "Types.lean", "slhdsa")).issubset(decls(root / "lean/Slhdsa/Types.lean", "slhdsa")):
        raise ValueError("buffered subtree input types changed")
    return prefix + "\n\n".join(out) + "\nend slhdsa.Buffered\n"


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        crate = folder / "crate"
        crate.mkdir()
        for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
            file = root / "rust" / name
            if file.exists():
                shutil.copy(file, crate / name)
        shutil.copytree(root / "rust/src", crate / "src")
        (crate / "benches").mkdir()
        (crate / "benches/platforms.rs").touch()
        src = crate / "src/shake/batch.rs"
        src.write_text(lift_rows(src.read_text()))
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            extracted = folder / target
            extracted.mkdir()
            pkg = facade["extract"](crate, target, "Buffered", extracted, ["crate::shake::batch::xmss_subtree"], cuts)
            if program(pkg) != dest.read_text():
                raise ValueError(f"{target} projected program changed")
            print(f"{target}: all 15 buffered subtree declarations matched", flush=True)

    module = "Buffered.Store"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](module, [
        "slhdsa.Buffered." + theorem for theorem in (
            "carry_gather", "flush_gather", "hashed_gather", "stored_cells", "full_store", "prefix_store"
        )
    ])


if __name__ == "__main__":
    main()
