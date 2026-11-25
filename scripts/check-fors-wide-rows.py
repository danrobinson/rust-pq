#!/usr/bin/env python3
"""Replay the production FORS packed slice loops on Apple and x86-64."""
from pathlib import Path
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
module = lean / "Cachepath/NativeVerify/ForsWideRowsProgram.lean"
roots = ["crate::shake::fors_batch::" + name for name in ("batch_leaves_slice", "batch_pairs_slice")]
cuts = ["crate::shake::fors_batch::fors_leaves_fused", "crate::shake::batch", "crate::shake256"]


def program(package):
    expected = {"shake.batch.pair_active", "shake.fors_batch.fors_leaves_fused", "shake256.parallel.WIDTH"}
    if set(re.findall(r"^axiom ([\w.]+)", (package / "FunsExternal_Template.lean").read_text(), re.M)) != expected:
        raise ValueError("unrecognized FORS slice dependency")
    baseline = lean.parent / "lean/Slhdsa"
    if not set(decls(package / "Types.lean", "slhdsa")).issubset(decls(baseline / "Types.lean", "slhdsa")):
        raise ValueError("unrecognized FORS slice input types")
    known = set(decls(baseline / "Funs.lean", "slhdsa"))
    out = []
    for body in decls(package / "Funs.lean", "slhdsa"):
        if not re.search(r"\bdef shake\.fors_batch\.batch_(leaves|pairs)_slice", body):
            if body not in known:
                raise ValueError("unrecognized FORS slice helper: " + body)
            continue
        for old, new in (("shake.fors_batch.batch_leaves_slice", "leaves"),
                         ("shake.fors_batch.batch_pairs_slice", "pairs"),
                         ("shake.batch.pair_active", "(ActiveHash.pair_active kernel.active)"),
                         ("shake.fors_batch.fors_leaves_fused", "(ForsFused.fused kernel.active)"),
                         ("shake256.parallel.WIDTH", "(ok 8#usize : Result Usize)")):
            body = body.replace(old, new)
        out.append(body)
    if len(out) != 8:
        raise ValueError(f"expected all eight FORS slice declarations, got {len(out)}")
    return ("import Cachepath.NativeVerify.ForsFused\nimport Fused.Program\n"
            "open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace slhdsa.NativeVerify.ForsWideRows\n"
            "open ShakeBatch\nset_option linter.concreteInstances false\nvariable [kernel : Fused.Kernel]\n"
            "local instance rowsProgramMachine : Machine := Fused.machine kernel\n\n" +
            "\n\n".join(out) + "\nend slhdsa.NativeVerify.ForsWideRows\n")


def main():
    with tempfile.TemporaryDirectory() as temp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            folder = Path(temp) / target
            folder.mkdir()
            width = facade["extract"]("rust", target, "Width", folder, ["crate::shake256::parallel::WIDTH"], [])
            if "@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := 8#usize" not in decls(width / "Funs.lean", "slhdsa"):
                raise ValueError(f"unexpected lane count on {target}")
            pkg = facade["extract"]("rust", target, "Exact", folder, roots, cuts)
            if program(pkg) != module.read_text():
                raise ValueError(f"{target} FORS slice model differs from the native extraction")
            print(f"{target}: matched all eight FORS slice declarations", flush=True)

    for suffix, names in (("Leaves", ("leaves_spec",)), ("Pairs", ("gather", "pairs_spec"))):
        mod = "Cachepath.NativeVerify.ForsWideRows" + suffix
        facade["run"](["lake", "build", mod], lean)
        facade["audit_theorems"](mod, ["slhdsa.NativeVerify.ForsWideRows." + name for name in names])


if __name__ == "__main__":
    main()
