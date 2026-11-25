#!/usr/bin/env python3
"""Check the active-lane, zero-copy FORS recovery program against the Rust on each hosted target."""
import os
import re
import subprocess
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
    expected_calls = {"core.num.U32.swap_bytes", "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter",
                      "shake.batch.seed_words", "shake.batch.adrs_words", "shake.fors_batch.word",
                      "shake256.Sponge.absorb", "shake256.parallel.permute_active", "shake.hash.digest", "shake.hash.start"}
    calls = set(re.findall(r"^axiom ([\w.]+)", (package / "FunsExternal_Template.lean").read_text(), re.M))
    state_types = set(re.findall(r"^axiom ([\w.]+)", (package / "TypesExternal_Template.lean").read_text(), re.M))
    if calls != expected_calls or state_types != {"shake256.Sponge"}:
        raise ValueError(f"{target}: unexpected recovery cutpoints: {calls ^ expected_calls}, {state_types}")
    print(f"{target}: matched {len(actual)} zero-copy FORS recovery declarations", flush=True)


def check_dispatch(target, scratch):
    entrypoint = "crate::shake::fors::fors_pk_from_sig"
    caller = facade["extract"]("rust", target, "ForsEntry", scratch, [entrypoint],
                               ["crate::shake::batch", "crate::shake::fors_batch", "crate::shake::hash",
                                "crate::shake::xmss", "crate::shake256", "crate::util"])
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    matched = []
    for item in decls(caller / "Funs.lean", "slhdsa"):
        if item.startswith("def shake.fors.fors_pk_from_sig\n"):
            matched.append(item)
        elif item not in known:
            raise ValueError(f"{target}: unknown FORS dispatcher dependency: {item}")
    if len(matched) != 1:
        raise ValueError(f"{target}: missing FORS dispatcher")
    extracted = matched[0].replace("def shake.fors.fors_pk_from_sig", "def actual")
    extracted = extracted.replace("shake.fors_batch.recover", "NativeVerify.Fors.recover")
    extracted = extracted.replace("shake.batch.available", "available")
    source = f"""import Cachepath.NativeVerify.ForsRecovery
open Aeneas Aeneas.Std Result slhdsa
namespace Replay
variable [m : ShakeBatch.Machine] [s : ShakeBatch.Stream] [kernel : NativeVerify.Fors.ActiveKernel m]
variable (available : Usize → Result Bool)
{extracted}
example : @actual m s kernel available = @NativeVerify.Fors.dispatched m kernel s available := rfl
end Replay"""
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input=source, text=True)
    print(f"{target}: matched native FORS dispatcher, including its portable fallback", flush=True)


def reject_reversed_parity(scratch):
    inputs = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
    crate = inputs["copy_rust_crate"](scratch)
    rust = crate / "src/shake/fors_batch.rs"
    original = rust.read_text()
    parity = "if idx & 1 == 0 {"
    if original.count(parity) != 1:
        raise ValueError("native FORS parity selection changed")
    rust.write_text(original.replace(parity, "if idx & 1 != 0 {"))
    raw = facade["extract"](crate, "aarch64-apple-darwin", "WrongParity", scratch, [entry], cuts, includes)
    installed = re.search(r"def recover_loop0_loop4_loop1\.body\b[\s\S]*?(?=\n\n)", program.read_text())[0]
    fresh = next(d for d in decls(raw / "Funs.lean", "slhdsa") if "def shake.fors_batch.recover_loop0_loop4_loop1.body" in d)
    fresh = link(fresh[fresh.index("def "):], 8)
    if fresh.split() == installed.split() or program.read_text().count(installed) != 1:
        raise ValueError("could not locate the translated parity mutation")
    model = scratch / "Cachepath/NativeVerify"
    model.mkdir(parents=True)
    # Lean resolves a package through its first directory on LEAN_PATH.
    cache = lean / ".lake/build/lib/lean/Cachepath"
    for compiled in cache.iterdir():
        if compiled.name != "NativeVerify":
            (model.parent / compiled.name).symlink_to(compiled)
    for compiled in (cache / "NativeVerify").iterdir():
        if not compiled.name.startswith("ForsProgram."):
            (model / compiled.name).symlink_to(compiled)
    changed = model / program.name
    changed.write_text(program.read_text().replace(installed, fresh))
    search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean, text=True).strip()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(scratch), search]))
    facade["run"](["lean", "--root", scratch, "-o", changed.with_suffix(".olean"), changed], lean, env=env)
    checked = subprocess.run(["lean", lean / "Cachepath/NativeVerify/ForsParents.lean"], cwd=lean,
                             env=env, capture_output=True, text=True)
    if checked.returncode == 0 or "error:" not in checked.stdout or "idx &&&" not in checked.stdout:
        raise ValueError("expected the parent routing proof to reject inverted parity: " + checked.stdout)
    print("Lean rejected the native Rust mutation that reverses every FORS sibling", flush=True)


if __name__ == "__main__":
    facade["run"](["lake", "build", "Cachepath.NativeVerify.ForsRecovery"], lean)
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            package = facade["extract"]("rust", target, "ForsVerify", Path(tmp), [entry], cuts, includes)
            validate(package, target)
            check_dispatch(target, Path(tmp))
    roots = {
        "Indices": ["indices_spec"],
        "Payload": ["pair_payloads"],
        "Rows": ["seed_rows", "leaf_payload", "snapshot"],
        "LeafHash": ["leaf_fips", "split_batch"],
        "Parents": ["parent_lanes"],
        "PairFips": ["parent_fips"],
        "Recovery": ["native_recovery", "dispatched_fips"],
        "Padding": ["zero_leaf_tail", "zero_pair_tail", "pad_pair_word"],
        "Digest": ["extract_bytes", "append_batch"],
    }
    for name, theorems in roots.items():
        module = f"Cachepath.NativeVerify.Fors{name}"
        facade["run"](["lake", "build", module], lean)
        facade["audit_theorems"](module, ["slhdsa.NativeVerify.Fors." + thm for thm in theorems])
    with tempfile.TemporaryDirectory() as tmp:
        reject_reversed_parity(Path(tmp))
