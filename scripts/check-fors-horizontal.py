#!/usr/bin/env python3
"""Bind FORS TreeHash's horizontal carry, flush and fused leaf batches to Rust."""
from pathlib import Path
import os
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
common = runpy.run_path(str(HERE / "check-shake-buffered-program.py"))
facade, lean = common["facade"], common["lean"]
root = lean.parent
dest = lean / "Buffered/ForsHorizontal/Program.lean"
name = "shake.fors_batch.fors_subtree_horiz"


def program(pkg):
    types = (pkg / "Types.lean").read_text()
    calls = (pkg / "Funs.lean").read_text()
    known = set(common["decls"](root / "lean/Slhdsa/Funs.lean", "slhdsa"))
    for decl in common["decls"](pkg / "Funs.lean", "slhdsa"):
        if name not in decl and decl not in known:
            raise ValueError("unexpected FORS subtree dependency " + decl)
    external = set(re.findall(r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M))
    if external != {"shake.batch.pair_active", "shake.fors_batch.fors_leaves_fused", "shake.hash.thash_pair"}:
        raise ValueError(f"unexpected FORS subtree cut points {external}")
    portable = set(common["decls"](root / "lean/Slhdsa/Types.lean", "slhdsa"))
    for decl in common["decls"](pkg / "Types.lean", "slhdsa"):
        if name not in decl and decl not in portable:
            raise ValueError("unexpected FORS subtree type " + decl)
    body = types[types.index("@[reducible]"):types.rindex("end slhdsa")] + "\n" + calls[
        calls.index("def\n  " + name + ".closure"):calls.rindex("end slhdsa")]
    body = re.sub(r"/--[\s\S]*?-/", "", body)
    for before, after in [(name, "subtree"), ("shake.fors_batch.fors_leaves_fused", "(ForsFused.fused kernel.active)"),
                          ("shake.batch.pair_active", "(ActiveHash.pair_active kernel.active)")]:
        body = body.replace(before, after)
    return ("import Cachepath.NativeVerify.ForsFused\nimport Fused.Program\n"
            "open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace slhdsa.ForsHorizontal\n"
            "open ShakeBatch NativeVerify\nset_option linter.concreteInstances false\nvariable [kernel : Fused.Kernel]\n"
            "local instance : Machine := Fused.machine kernel\n\n" + body.strip() + "\n\nend slhdsa.ForsHorizontal\n")


def main():
    os.environ["PATH"] = f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    copier = runpy.run_path(str(HERE / "check-cache-endtoend.py"))["copy_rust_crate"]
    with tempfile.TemporaryDirectory() as d:
        folder = Path(d)
        crate = copier(folder)
        file = crate / "src/shake/fors_batch.rs"
        file.write_text(common["lift_rows"](file.read_text(), "fors_subtree_horiz"))
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            out = folder / target
            out.mkdir()
            pkg = facade["extract"](crate, target, "Horiz", out, ["crate::shake::fors_batch::fors_subtree_horiz"],
                ["crate::shake::fors_batch::fors_leaves_fused", "crate::shake::batch::pair_active",
                 "crate::shake::hash::thash_pair", "crate::shake256"])
            if program(pkg).split() != dest.read_text().split():
                raise ValueError(f"{target} horizontal FORS subtree changed")
            calls = pkg / "Funs.lean"
            original = calls.read_text()
            for before, after in (("let base_leaf ← first_leaf + i6", "let base_leaf ← first_leaf + 0#u32"),
                                  ("if count = 1#usize", "if count = 2#usize")):
                if original.count(before) != 1:
                    raise ValueError("review the horizontal subtree mutation anchors")
                calls.write_text(original.replace(before, after))
                if program(pkg).split() == dest.read_text().split():
                    raise ValueError("accepted a changed leaf batch index or flush count")

    module = "Buffered.ForsHorizontal.Entry"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](module, ["slhdsa.ForsHorizontal." + n for n in
        ("indices_spec", "carry", "flush_transfer", "flush", "blocks", "subtree_spec")])

    for probe in ("fors_buffered.py", "fors_buffered_symbolic.py"):
        facade["run"](["uv", "run", "--script", HERE / "parallel-proof" / probe], root)


if __name__ == "__main__":
    main()
