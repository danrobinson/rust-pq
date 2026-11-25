#!/usr/bin/env python3
"""Check the active-lane, zero-copy FORS recovery program against the Rust on each hosted target."""
import re
import runpy
import tempfile
from pathlib import Path

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, lean, decls = shared["facade"], shared["lean"], shared["decls"]
entry = "crate::shake::fors_batch::recover"
cuts = ["crate::shake::fors_batch::word", "crate::shake::batch::seed_words", "crate::shake::batch::adrs_words",
        "crate::shake::hash::start", "crate::shake::hash::digest", "crate::shake256"]
includes = ["crate::shake256::parallel::WIDTH"]
program = lean / "Cachepath/NativeVerify/ForsProgram.lean"


def link(item, width):
    item = re.sub(r"(Array\s+Std\.U(?:32|64)\s+|Array\.repeat\s+)" + str(width) + r"#usize",
                  r"\g<1>machine.width", item)
    for old, new in (("shake.fors_batch.recover", "recover"), ("shake.batch.seed_words", "seed_words"),
                     ("shake.batch.adrs_words", "adrs_words"), ("shake.fors_batch.word", "ShakeBatch.shake.batch.word"),
                     ("shake256.Sponge.absorb", "stream.absorb"), ("shake256.Sponge", "stream.State"),
                     ("shake.hash.start", "stream.start"), ("shake.hash.digest", "stream.digest"),
                     ("shake256.parallel.permute_active", "accelerator.run"), ("shake256.parallel.WIDTH", "machine.width"),
                     ("core.num.U32.swap_bytes", "ShakeBatch.core.num.U32.swap_bytes"),
                     ("MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter", "core.slice.Slice.iter_mut")):
        item = item.replace(old, new)
    return item


def validate(package, target):
    width = 3 if target == "aarch64-unknown-linux-gnu" else 8
    actual = []
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    for item in decls(package / "Funs.lean", "slhdsa"):
        if "def shake.fors_batch.recover" in item:
            actual.append(link(item, width))
        elif item not in known and item != f"@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := {width}#usize":
            raise ValueError(f"{target}: unmatched FORS dependency: {item}")
    expected = [item for item in decls(program, "slhdsa.NativeVerify.Fors") if "def recover" in item]
    if [x.split() for x in actual] != [x.split() for x in expected]:
        raise ValueError(f"{target}: active-lane FORS recovery differs from its Lean translation")
    print(f"{target}: matched {len(actual)} zero-copy FORS recovery declarations", flush=True)


if __name__ == "__main__":
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            package = facade["extract"]("rust", target, "ForsVerify", Path(tmp), [entry], cuts, includes)
            validate(package, target)
    roots = {
        "Indices": ["indices_spec"],
        "Payload": ["pair_payloads"],
        "Rows": ["seed_rows", "leaf_payload", "snapshot"],
        "LeafHash": ["leaf_fips", "split_batch"],
        "Parents": ["parent_lanes"],
        "Padding": ["zero_leaf_tail", "zero_pair_tail", "pad_pair_word"],
        "Digest": ["extract_bytes", "append_batch"],
    }
    for name, theorems in roots.items():
        module = f"Cachepath.NativeVerify.Fors{name}"
        facade["run"](["lake", "build", module], lean)
        facade["audit_theorems"](module, ["slhdsa.NativeVerify.Fors." + thm for thm in theorems])
