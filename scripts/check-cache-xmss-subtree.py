#!/usr/bin/env python3
"""Bind the vectorized cached XMSS subtree reducer to the hosted Rust extractions."""
from pathlib import Path
import os
import runpy
import subprocess
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
simd = "crate::cache::shake_ops::simd::"
cuts = [simd + n for n in ("fill_xmss_leaves", "hash_pairs", "wots_pk_gen_single")]
cuts += ["crate::cache::shake_ops::thash_pair"]


def linked(path):
    result = []
    scalar = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    types = set(decls(lean.parent / "lean/Slhdsa/Types.lean", "slhdsa"))
    if set(decls(path.with_name("Types.lean"), "slhdsa")) - types:
        raise ValueError("unexpected subtree types")
    for item in decls(path, "slhdsa"):
        if item in scalar:
            continue
        item = item.replace("cache.shake_ops.simd.xmss_node", "node")
        for name, model in (("hash_pairs", "Backend.pairs"), ("fill_xmss_leaves", "Backend.fill"),
                            ("wots_pk_gen_single", "Single.leaf")):
            item = item.replace("cache.shake_ops.simd." + name, model)
        item = item.replace("cache.shake_ops.thash_pair", "shake.hash.thash_pair")
        result.append(item)
    return result


def check_address_mutation(scratch, expected):
    source_tools = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
    crate = source_tools["copy_rust_crate"](scratch)
    rust = crate / "src/cache.rs"
    source = rust.read_text()
    shift = "let level_base = (i as usize) << (z - h);"
    if source.count(shift) != 1:
        raise ValueError("could not locate the production subtree level address")
    rust.write_text(source.replace(shift, "let level_base = (i as usize) << (z - h + 1);"))
    package = facade["extract"](crate, facade["TARGETS"][0], "WrongAddress", scratch, [simd + "xmss_node"], cuts)
    mutated = linked(package / "Funs.lean")
    if len(mutated) != len(expected) or mutated[0] == expected[0] or mutated[1:] != expected[1:]:
        raise ValueError("unexpected extraction for shifted subtree address")
    module = "SubtreeProgram"
    directory = scratch / "Cachepath"
    directory.mkdir()
    for compiled in (lean / ".lake/build/lib/lean/Cachepath").iterdir():
        if not compiled.name.startswith(module + "."):
            (directory / compiled.name).symlink_to(compiled)
    template = (lean / "Cachepath" / (module + ".lean")).read_text()
    if template.count(expected[0]) != 1:
        raise ValueError("could not install the translated loop body")
    program = directory / (module + ".lean")
    program.write_text(template.replace(expected[0], mutated[0]))
    search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean, text=True).strip()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(scratch), search]))
    facade["run"](["lean", "--root", scratch, "-o", program.with_suffix(".olean"), program], lean, env=env)
    rejected = subprocess.run(["lean", lean / "Cachepath/Subtree.lean"], cwd=lean, env=env,
                              capture_output=True, text=True)
    if rejected.returncode == 0 or "error:" not in rejected.stdout or "level_base" not in rejected.stdout:
        raise ValueError("expected a subtree loop proof failure for doubled parent addresses\n" + rejected.stdout)
    print("Lean rejected a source mutation that doubles every parent-row address", flush=True)


if __name__ == "__main__":
    expected = [d for d in decls(lean / "Cachepath/SubtreeProgram.lean",
                                 "slhdsa.cache.builder.nativeShake.Subtree") if "def node" in d]
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            package = facade["extract"]("rust", target, "FastNode", Path(tmp), [simd + "xmss_node"], cuts)
            if linked(package / "Funs.lean") != expected:
                raise ValueError(f"cached SIMD subtree changed on {target}")
            probe = facade["extract"]("rust", target, "Probe", Path(tmp), [simd + "available"],
                                      ["crate::shake256::parallel::available"])
            (body,) = decls(probe / "Funs.lean", "slhdsa")
            body = body.replace("cache.shake_ops.simd.available", "shake.batch.available")
            body = body.replace("shake256.parallel.available", "hardware")
            if body not in (lean / "Shakebatch/Available.lean").read_text():
                raise ValueError(f"cache SHAKE feature selection changed on {target}")
            print(f"{target}: matched the subtree reducer and feature selection", flush=True)
    facade["run"](["lake", "build", "Cachepath.NativePlatforms"], lean)
    facade["audit_theorems"]("Cachepath.NativePlatforms", [
        "CacheopsRust.NativeSession.linuxArm", "CacheopsRust.NativeSession.linuxX86",
        "CacheopsRust.NativeSession.appleArm", "CacheopsRust.NativeSession.appleFull",
        "CacheopsRust.NativeSession.linuxArmFull", "CacheopsRust.NativeSession.linuxX86Full"])
    facade["audit_theorems"]("Cachepath.NativeSession", [
        "CacheopsRust.NativeSession.dispatch", "CacheopsRust.NativeSession.builder",
        "CacheopsRust.NativeSession.keygen_sign_many", "CacheopsRust.NativeSession.keygen_sign_verify_with_precompute"])
    facade["audit_theorems"]("Cachepath.Subtree", ["slhdsa.cache.builder.nativeShake.Subtree.node_eq_scalar"])
    with tempfile.TemporaryDirectory() as tmp:
        check_address_mutation(Path(tmp), expected)
