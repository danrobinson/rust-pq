#!/usr/bin/env python3
"""Run the whole FORS planner with a fresh symbolic word per decoded tree index."""

from pathlib import Path
import os
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
gate = runpy.run_path(str(HERE / "check-parallel-fors-ownership.py"))


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError(f"FORS planner type boundary changed near {before}")
    return text.replace(before, after)


def generic(program):
    planner, observer = program.split("// The source gate inserts")
    for before, after in [
        ("struct ForsSplitMeta {", "struct ForsSplitMeta<I> {"),
        ("root_idx: u32,", "root_idx: I,"),
        ("enum WorkKind {", "enum WorkKind<I> {"),
        ("ForsNodeDirect { idx: u32,", "ForsNodeDirect { idx: I,"),
        ("ForsNodeSplit { idx: u32,", "ForsNodeSplit { idx: I,"),
        ("struct WorkItem {", "struct WorkItem<I> {"),
        ("kind: WorkKind,", "kind: WorkKind<I>,"),
        ("fn build<const WIDTH:usize>", "fn build<const WIDTH:usize,I>"),
        ("fors_indices:&[u32]", "fors_indices:&[I]"),
        (
            "(Vec<WorkItem>,Vec<ForsSplitMeta>,usize) {",
            """(Vec<WorkItem<I>>,Vec<ForsSplitMeta<I>>,usize)
            where I:Copy + std::ops::Shr<u32,Output=I> + std::ops::Shl<u32,Output=I>
                + std::ops::BitXor<u32,Output=I> + std::ops::Add<u32,Output=I>,
                u32:std::ops::Add<I,Output=I> {""",
        ),
        ("Vec<ForsSplitMeta> = Vec::new()", "Vec<ForsSplitMeta<I>> = Vec::new()"),
    ]:
        planner = replace_once(planner, before, after)
    observer = replace_once(
        "// The source gate inserts" + observer, "build::<WIDTH>", "build::<WIDTH,_>"
    )
    return planner, observer


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    raw = gate["build_source"]()
    plan, observer = generic(raw)
    symbols = (HERE / "parallel-proof/planner-symbols.rs").read_text()
    symbolic_observer = replace_once(
        observer,
        ".map(|t| ((t as u32) * 6143 + 111) % (1 << a))",
        ".map(symbolic::Word::choice)",
    )
    geometry = re.findall(
        r"pub const SHA2_(?:128|192|256)[SF]: Params = Params \{[^}]*? a: (\d+), k: (\d+),",
        (gate["root"] / "rust/src/params.rs").read_text(),
    )
    if len(geometry) != 6:
        raise ValueError("missing standard parameter geometry")
    args = [v for pair in geometry for v in pair]
    with tempfile.TemporaryDirectory() as tmp:
        source, exe = Path(tmp, "planner.rs"), Path(tmp, "planner")

        def execute(code, build=True):
            source.write_text(code)
            compile = subprocess.run(
                ["rustc", "--edition=2021", "-Awarnings", source, "-o", exe],
                capture_output=True,
            )
            if build is False:
                if compile.returncode == 0 or b"binary operation" not in compile.stderr:
                    raise ValueError(
                        "digest-dependent branch escaped abstract-index type checking"
                    )
                return
            compile.check_returncode()
            return subprocess.run([exe, *args], capture_output=True)

        concrete = execute(raw)
        concrete.check_returncode()
        for code in [plan + observer, plan + symbols + symbolic_observer]:
            result = execute(code)
            result.check_returncode()
            if result.stdout != concrete.stdout:
                raise ValueError("symbolic indices changed queue ownership")
        fault = replace_once(
            plan,
            "if WIDTH == 8 {",
            "if WIDTH == 8 && fors_indices[0] == fors_indices[1] {",
        )
        execute(fault + symbols + symbolic_observer, build=False)
        for old, new in [
            ("((idx >> j) ^ 1)", "((idx >> j) ^ 0)"),
            ("(root_idx << split) + c as u32", "(root_idx << split) + 0u32"),
        ]:
            if (
                old not in plan
                or execute(
                    plan.replace(old, new) + symbols + symbolic_observer
                ).returncode
                == 0
            ):
                raise ValueError("symbolic index corruption passed the queue observer")
    print(
        "All 24 FORS queue configurations matched with symbolic digest indices, including every issued root and split child."
    )


if __name__ == "__main__":
    main()
