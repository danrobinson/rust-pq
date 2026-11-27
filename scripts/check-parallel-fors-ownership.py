#!/usr/bin/env python3
"""Compare every emitted FORS field and split chunk with Lean's unique-owner function."""

import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
gate = runpy.run_path(str(HERE / "check-parallel-forest-pack.py"))
root, lean = gate["common"]["ROOT"], gate["lean"]


def build_source():
    raw = (root / "rust/src/slh/parallel.rs").read_text()
    sign = gate["ticket"]["shared"]["signer"].function(raw, "sign")
    types = raw[raw.index("struct ForsSplitMeta") : raw.index("pub(super) fn sign")]
    body = sign[
        sign.index("let fors_stride =") : sign.index("// Order largest-work-first")
    ]
    body = body.replace(
        "if super::super::batch::available::<N>() {", "if simd {"
    ).replace("use crate::shake256::parallel::WIDTH;", "")
    return (
        """#![allow(dead_code)]
macro_rules! shake_only { ($($i:tt)*) => {$($i)*} }
struct Params {k:u32}
"""
        + types
        + """
fn build<const WIDTH:usize>(a:u32,k:usize,simd:bool,fors_indices:&[u32])->(Vec<WorkItem>,Vec<ForsSplitMeta>,usize) {
    let p=Params{k:k as u32};
    let mut jobs=Vec::new();
"""
        + body
        + "(jobs,fors_split_meta,fors_split_count)\n}\n"
        + (HERE / "parallel-proof/fors-ownership.rs").read_text()
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    facade = gate["ticket"]["shared"]["facade"]
    facade["run"](["lake", "build", "Parallel.ForsSharedGroup"], lean)
    geometry = re.findall(
        r"pub const SHA2_(?:128|192|256)[SF]: Params = Params \{[^}]*? a: (\d+), k: (\d+),",
        (root / "rust/src/params.rs").read_text(),
    )
    if len(geometry) != 6:
        raise ValueError("expected six standardized FORS geometries")
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        driver = folder / "owners.lean"
        driver.write_text(
            """import Parallel.ForsCover
open slhdsa.RawFors
def main : IO Unit := do
  for (a,k) in (["""
            + ",".join(f"({a},{k})" for a, k in geometry)
            + """] : List (Nat × Nat)) do
    for p in [Policy.scalar,.three,.eight,.scalar] do
      for t in [:k] do
        for c in [:a+1] do
          match owner p a t c with
          | .low f l c => IO.println s!"0 {f} {l} {c}"
          | .direct f l h => IO.println s!"1 {f} {l} {h}"
          | .reduced t h => IO.println s!"2 {t} 0 {h}"
"""
        )
        expected = subprocess.run(
            ["lake", "env", "lean", "--run", driver],
            cwd=lean,
            check=True,
            capture_output=True,
        ).stdout
        src = build_source()
        rust = folder / "plan.rs"
        binary = folder / "plan"
        for old, new in [
            (None, None),
            ("let low_h = a.min(3);", "let low_h = a.min(2);"),
            ("slot: slot_start + c,", "slot: slot_start,"),
        ]:
            rust.write_text(src if old is None else src.replace(old, new))
            subprocess.run(
                ["rustc", "--edition=2021", "-Awarnings", rust, "-o", binary],
                check=True,
            )
            run = subprocess.run(
                [binary, *[v for pair in geometry for v in pair]], capture_output=True
            )
            if (run.returncode == 0 and run.stdout == expected) != (old is None):
                raise ValueError(f"unexpected ownership comparison: {old}")
    facade["audit_theorems"](
        "Parallel.ForsSharedGroup",
        [
            "slhdsa.RawFors." + n
            for n in (
                "unique",
                "complete",
                "Receipt.correct",
                "pack_spec",
                "native_receipt",
                "shared_low",
                "shared_direct",
                "shared_scalar",
            )
        ],
    )


if __name__ == "__main__":
    main()
