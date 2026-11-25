#!/usr/bin/env python3
"""Bind both phases of the packed FORS leaf computation to fresh Rust extraction."""
from pathlib import Path
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
dest = lean / "Cachepath/NativeVerify/ForsFusedProgram.lean"
source = "shake.fors_batch.fors_leaves_fused"


def program(package, width):
    prefix = """import Cachepath.NativeVerify.ActiveHashProgram
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsFused
open ShakeBatch
variable [machine : Machine] (permute : Active machine)
"""
    bodies = []
    for body in decls(package / "Funs.lean", "slhdsa"):
        if not re.search(r"\bdef " + re.escape(source), body.partition(":=")[0]):
            continue
        body = re.sub(r"(Array\.repeat\s+|Std\.U(?:32|64)\s+|Std\.U8\s+N\)\s+)" +
                      str(width) + r"#usize", r"\g<1>machine.width", body)
        body = body.replace(source, "fused")
        for old, new in (("shake.batch.seed_words", "NativeVerify.seed_words"),
                         ("shake.batch.adrs_words", "NativeVerify.adrs_words"),
                         ("shake256.parallel.permute_active", "permute"),
                         ("core.num.U32.swap_bytes", "ShakeBatch.core.num.U32.swap_bytes"),
                         ("MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter", "core.slice.Slice.iter_mut")):
            body = body.replace(old, new)
        bodies.append(body)
    if len(bodies) != 13:
        raise ValueError(f"expected all 13 FORS declarations, got {len(bodies)}")
    return prefix + "\n\n".join(bodies) + "\nend slhdsa.NativeVerify.ForsFused\n"


def main():
    os.environ["PATH"] = f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"]:
            package = facade["extract"]("rust", target, "Fused", Path(tmp),
                ["crate::shake::fors_batch::fors_leaves_fused"],
                ["crate::shake::batch::seed_words", "crate::shake::batch::adrs_words", "crate::shake256"],
                ["crate::shake256::parallel::WIDTH"])
            width = 3 if "aarch64-unknown" in target else 8
            portable = lean.parent / "lean/Slhdsa"
            deps = set(decls(portable / "Funs.lean", "slhdsa"))
            deps.add(f"@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := {width}#usize")
            for decl in decls(package / "Funs.lean", "slhdsa"):
                if source not in decl and decl not in deps:
                    raise ValueError(f"{target} unrecognized FORS dependency: {decl}")
            types = set(decls(package / "Types.lean", "slhdsa"))
            if not types.issubset(decls(portable / "Types.lean", "slhdsa")):
                raise ValueError(f"{target} FORS argument types changed")
            cutpoints = set(re.findall(r"^axiom ([\w.]+)", (package / "FunsExternal_Template.lean").read_text(), re.M))
            expected = {"core.num.U32.swap_bytes", "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter",
                        "shake.batch.seed_words", "shake.batch.adrs_words", "shake256.parallel.permute_active"}
            if cutpoints != expected:
                raise ValueError(f"{target} FORS cutpoints changed: {cutpoints ^ expected}")
            if program(package, width) != dest.read_text():
                raise ValueError(f"{target} fused FORS program changed")
            print(f"{target}: matched all 13 fused FORS declarations", flush=True)
    module = "Cachepath.NativeVerify.ForsFused"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](module, ["slhdsa.NativeVerify.ForsFused.leaf_correct"])


if __name__ == "__main__":
    main()
