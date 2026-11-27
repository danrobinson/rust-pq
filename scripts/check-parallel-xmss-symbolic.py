#!/usr/bin/env python3
"""Match the complete production XMSS enqueue loop to Lean's physical chunk coordinates."""

import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
fors = runpy.run_path(str(HERE / "check-parallel-fors-symbolic.py"))
root = fors["gate"]["root"]
lean = fors["gate"]["lean"]
replace = fors["replace_once"]


def program():
    raw = (root / "rust/src/slh/parallel.rs").read_text()
    records = raw[raw.index("struct XmssAuthMeta") : raw.index("pub(super) fn sign")]
    for old, new in [
        ("struct XmssAuthMeta {", "struct XmssAuthMeta<I> {"),
        (
            "struct XmssAuthMeta<I> {\n    slot_start: usize,\n    split: u32,\n    root_idx: u32,",
            "struct XmssAuthMeta<I> {\n    slot_start: usize,\n    split: u32,\n    root_idx: I,",
        ),
        ("enum WorkKind {", "enum WorkKind<I> {"),
        (
            "XmssSubtree {\n        layer: u16,\n        idx: u32,",
            "XmssSubtree {\n        layer: u16,\n        idx: I,",
        ),
        ("struct WorkItem {", "struct WorkItem<I> {"),
        ("kind: WorkKind,", "kind: WorkKind<I>,"),
    ]:
        records = replace(records, old, new)
    start = raw.index("let mut jobs: Vec<WorkItem>")
    body = (
        raw[start : raw.index("// --- 2. FORS", start)]
        .replace("Vec<WorkItem>", "Vec<WorkItem<I>>")
        .replace("Vec<XmssAuthMeta>", "Vec<XmssAuthMeta<I>>")
    )
    return (
        "#![allow(dead_code)]\n"
        + records
        + """
        struct Params { hp:u32 }
        fn build<I>(p:&Params, d:usize, layers:&[((),I)]) -> (Vec<WorkItem<I>>,Vec<XmssAuthMeta<I>>,usize)
          where I:Copy + std::ops::Shr<u32,Output=I> + std::ops::Shl<u32,Output=I>
             + std::ops::BitXor<u32,Output=I> + std::ops::Add<u32,Output=I> {
          let hp=p.hp as usize;
        """
        + body
        + "(jobs,xmss_meta,xmss_slot_count)\n}\n"
        + (HERE / "parallel-proof/planner-symbols.rs").read_text()
        + (HERE / "parallel-proof/xmss-plan-symbolic.rs").read_text()
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    subprocess.run(
        ["lake", "build", "Parallel.RawChunkLayout"],
        cwd=lean,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    src = program()
    suites = re.findall(
        r"pub const SHA2_\d+[SF]: Params = Params \{([^}]+)\}",
        (root / "rust/src/params.rs").read_text(),
    )
    geometry = [
        tuple(int(re.search(rf"\b{f}: (\d+)", suite)[1]) for f in ("d", "hp"))
        for suite in suites
    ]
    if len(geometry) != 6:
        raise ValueError("incomplete geometry")
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        witness = folder / "geometry.lean"
        witness.write_text(
            "import Parallel.RawChunkLayout\nopen slhdsa.ParallelRawChunks\ndef main : IO Unit := do\n"
            + f"  for (d,w) in ([{','.join(map(str, geometry))}] : List (Nat × Nat)) do\n"
            + '    for (q,c) in slots w (d*w) do IO.println s!"{q} {c}"\n'
        )
        expected = subprocess.check_output(
            ["lake", "env", "lean", "--run", witness], cwd=lean
        )
        rust, exe = folder / "planner.rs", folder / "planner"
        for old, new in [
            (None, None),
            ("xmss_slot_count += chunks", "xmss_slot_count += 1"),
            ("(root_idx << split) + c as u32", "(index << split) + c as u32"),
        ]:
            rust.write_text(src if old is None else replace(src, old, new))
            subprocess.run(
                ["rustc", "--edition=2021", "-Awarnings", rust, "-o", exe], check=True
            )
            run = subprocess.run(
                [exe, *[str(x) for pair in geometry for x in pair]], capture_output=True
            )
            if (run.returncode == 0 and run.stdout == expected) != (old is None):
                raise ValueError(f"unexpected XMSS projection: {old}")
    print(
        "Verified the full XMSS enqueue loop, including all symbolic indices, slot starts, weights, and signing-leaf tickets."
    )


if __name__ == "__main__":
    main()
