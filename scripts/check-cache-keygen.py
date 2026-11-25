#!/usr/bin/env python3
"""Replay Rust keygen_with_cache and audit its composition with repeated cached signing."""
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import tempfile

construction = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = construction["facade"], construction["decls"], construction["lean"]


def linked_caller(target, scratch, crate="rust"):
    cuts = construction["constructor_cuts"]
    package = facade["extract"](crate, target, "Keygen", scratch, ["crate::cache::keygen_with_cache"], cuts)
    if set(decls(package / "Types.lean", "slhdsa")) - set(decls(lean / "Cacheops/Types.lean", "CacheopsRust")):
        raise ValueError(f"unexpected keygen type on {target}")
    (caller,) = decls(package / "Funs.lean", "slhdsa")
    caller = caller.replace("def cache.keygen_with_cache", "def keygen")
    caller = caller.replace("(N : Std.Usize) (family", "(N : Std.Usize) (sha2 shake : cache.mutation.Builder N) (family")
    for family in ("sha2", "shake"):
        caller = caller.replace(f"cache.{family}_ops.build_xmss_tree", family)
    return caller, package


def replay(target, scratch):
    caller, package = linked_caller(target, scratch)
    cuts = construction["constructor_cuts"]
    if [caller] != decls(lean / "Cachepath/KeygenProgram.lean", "CacheopsRust.cache.generatedKeys"):
        raise ValueError(f"keygen_with_cache differs from the proved caller on {target}")
    checks = ["import Cachepath.Keygen", "open Aeneas Aeneas.Std Result CacheopsRust"]
    expected = {cut.removeprefix("crate::").replace("::", ".") for cut in cuts}
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    for external in facade["common"]["declarations"](template):
        name, signature = re.fullmatch(r"axiom (\S+)\s+(.*)", external, re.S).groups()
        expected.remove(name)
        if name.endswith(".build_xmss_tree"):
            signature = signature.replace("{N : Std.Usize}", "{N : Std.Usize} (builder : cache.mutation.Builder N)")
            binding = "builder"
        else:
            binding = "@" + name + " N"
        checks.append(f"example {signature} := {binding}")
    if expected:
        raise ValueError(f"unmatched keygen externals on {target}: {expected}")
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input="\n".join(checks), text=True)


def reject_wrong_seed(scratch):
    """A type-correct wrong write to SK.PKseed must invalidate the postcondition proof."""
    old = "sk[2 * N..3 * N].copy_from_slice(&pk_seed);"
    new = "sk[2 * N..3 * N].copy_from_slice(&sk_prf);"
    endtoend = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
    crate = endtoend["copy_rust_crate"](scratch)
    cache = crate / "src/cache.rs"
    original = cache.read_text()
    if original.count(old) != 1:
        raise ValueError("expected one generated secret key public seed write")
    cache.write_text(original.replace(old, new))
    caller, _ = linked_caller("aarch64-apple-darwin", scratch, crate)
    program = lean / "Cachepath/KeygenProgram.lean"
    (proved,) = decls(program, "CacheopsRust.cache.generatedKeys")
    if caller == proved:
        raise ValueError("wrong seed write still matches proved caller")
    modules = scratch / "Cachepath"
    shutil.copytree(lean / ".lake/build/lib/lean/Cachepath", modules)
    source = modules / "KeygenProgram.lean"
    source.write_text(program.read_text().split("def keygen", 1)[0] + caller + "\nend CacheopsRust.cache.generatedKeys\n")
    search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean, text=True).strip()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(scratch), search]))
    subprocess.run(["lean", "--root", scratch, "-o", modules / "KeygenProgram.olean", source],
                   cwd=lean, env=env, check=True)
    proof = lean / "Cachepath/Keygen.lean"
    fail = subprocess.run(["lean", proof], cwd=lean, env=env, capture_output=True, text=True)
    theorem_start = next(i for i, line in enumerate(proof.read_text().splitlines(), 1) if line.startswith("theorem keygen_spec "))
    errors = re.findall(r"Keygen\.lean:(\d+):\d+: error", fail.stdout + fail.stderr)
    if not fail.returncode or not errors or min(map(int, errors)) < theorem_start:
        raise ValueError("expected a failure inside keygen_spec for the altered write: " + fail.stdout + fail.stderr)
    print("Lean rejected a regenerated keygen that copies the PRF seed into SK.PKseed.", flush=True)


def main():
    facade["run"](["lake", "build", "Cachepath.KeygenVerify"], lean)
    with tempfile.TemporaryDirectory() as directory:
        for target in (*facade["TARGETS"], "riscv64gc-unknown-none-elf"):
            scratch = Path(directory) / target
            scratch.mkdir()
            replay(target, scratch)
            print(f"{target}: matched keygen_with_cache and all four external bindings", flush=True)
        reject_wrong_seed(Path(directory))
    facade["audit_theorems"]("Cachepath.KeygenVerify", [
        "CacheopsRust.cache.generatedKeys.keygen_spec",
        "CacheopsRust.Public.keygen_then_sign_many",
        "CacheopsRust.Public.scalar_keygen_then_sign_many",
        "CacheopsRust.Public.scalar_keygen_sign_verify",
    ])


if __name__ == "__main__":
    main()
