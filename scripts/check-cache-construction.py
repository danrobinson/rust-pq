#!/usr/bin/env python3
"""Compare the public cache constructor and both tree builders with fresh Aeneas output."""
from pathlib import Path
import re
import runpy
import tempfile

policy = runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))
facade, decls, lean = policy["facade"], policy["decls"], policy["lean"]
builders = ("crate::cache::sha2_ops::build_xmss_tree", "crate::cache::shake_ops::build_xmss_tree")
constructor_cuts = (*builders, "crate::cache::tree_root", "crate::util::block")
builder_cuts = ("crate::cache::level_offset", "crate::cache::tree_node_count",
                "crate::hash::seed_ctx", "crate::wots::wots_pk_gen", "crate::xmss::hash2")


def check_constructor(target, scratch):
    package = facade["extract"]("rust", target, "Constructor", scratch,
                                ["crate::cache::TopTreeCache::new"], constructor_cuts)
    shared_types = set(decls(lean / "Cacheops/Types.lean", "CacheopsRust"))
    if set(decls(package / "Types.lean", "slhdsa")) - shared_types:
        raise ValueError(f"changed constructor input types on {target}")
    (caller,) = decls(package / "Funs.lean", "slhdsa")
    caller = caller.replace("def cache.TopTreeCache.new", "def newCache")
    caller = caller.replace("(N : Std.Usize) (family", "(N : Std.Usize) (sha2 shake : cache.mutation.Builder N) (family")
    for family in ("sha2", "shake"):
        caller = caller.replace(f"cache.{family}_ops.build_xmss_tree", family)
    if [caller] != decls(lean / "Cachepath/ConstructorProgram.lean", "CacheopsRust.cache.constructor"):
        raise ValueError(f"public constructor differs from the proved caller on {target}")


def check_builder(target, scratch):
    package = facade["extract"]("rust", target, "Sha2Tree", scratch, [builders[0]], builder_cuts)
    portable = lean.parent / "lean/Slhdsa"
    for kind in ("Types", "Funs"):
        program = set(decls(portable / f"{kind}.lean", "slhdsa"))
        if kind == "Funs":
            program.update(decls(lean / "Cachepath/BuilderProgram.lean", "slhdsa"))
        fresh = set(decls(package / f"{kind}.lean", "slhdsa"))
        if fresh - program:
            raise ValueError(f"unmatched tree-builder declarations on {target}: {fresh - program}")
    externals = package / "FunsExternal_Template.lean"
    template = externals.read_text().split("open slhdsa", 1)[1]
    expected = {cut.removeprefix("crate::").replace("::", ".") for cut in builder_cuts}
    checks = ["import Cachepath.BuilderProgram", "open Aeneas Aeneas.Std Result slhdsa"]
    for decl in facade["common"]["declarations"](template):
        match = re.fullmatch(r"axiom (\S+)\s+(.*)", decl, re.S)
        if not match or match[1] not in expected:
            raise ValueError(f"unexpected external on {target}: {decl}")
        name, signature = match.groups()
        expected.remove(name)
        checks.append(f"example {signature} := {name}")
    if expected:
        raise ValueError(f"missing external calls on {target}: {expected}")
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input="\n".join(checks), text=True)


def check_shake(target, scratch, *, scalar_only=False):
    cuts = ("crate::cache::level_offset", "crate::cache::tree_node_count",
            "crate::cache::shake_ops::simd::available", "crate::cache::shake_ops::simd::hash_pairs",
            "crate::cache::shake_ops::simd::fill_xmss_leaves",
            "crate::cache::shake_ops::wots_pk_gen_portable", "crate::cache::shake_ops::thash_pair")
    if scalar_only:
        cuts = tuple(cut for cut in cuts if "::simd::" not in cut)
    package = facade["extract"]("rust", target, "ShakeTree", scratch, [builders[1]], cuts)
    program = (lean / "Cachepath/BuilderShakeProgram.lean").read_text()
    portable = lean.parent / "lean/Slhdsa"
    if set(decls(package / "Types.lean", "slhdsa")) - set(decls(portable / "Types.lean", "slhdsa")):
        raise ValueError(f"unexpected SHAKE tree type on {target}")
    functions = set(decls(portable / "Funs.lean", "slhdsa"))
    iterators = set(decls(lean / "Xmsskeys/Funs.lean", "XmssKeysRust"))
    aliases = {
        "cache.shake_ops.simd.available": "Backend.available",
        "cache.shake_ops.simd.hash_pairs": "Backend.pairs",
        "cache.shake_ops.simd.fill_xmss_leaves": "Backend.fill",
        "cache.shake_ops.wots_pk_gen_portable": "CacheScalar.cache.shake_ops.wots_pk_gen_portable",
        "cache.shake_ops.thash_pair": "shake.hash.thash_pair",
    }
    adapter = ("core.iter.adapters.enumerate.IteratorEnumerate.next",
               "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT",
               "core.iter.traits.iterator.Iterator.enumerate.trait_default")
    for declaration in decls(package / "Funs.lean", "slhdsa"):
        if declaration in functions or declaration in iterators:
            continue
        # Strip the Rust module prefix on this group's internal calls.
        # Token matching keeps the separately verified primitive bindings intact.
        pattern = r"cache\.shake_ops\.(?:simd\.)?[a-z_0-9]+"
        linked = re.sub(pattern, lambda m: aliases.get(m[0], m[0].removeprefix("cache.shake_ops.")), declaration)
        for method in adapter:
            linked = linked.replace(method, "XmssKeysRust." + method)
        if scalar_only:
            for old, new in (("fill_leaves_chunk", "portableLeaves"), ("build_xmss_tree_loop0.body", "portableLevel")):
                if f"def {old}\n" in linked:
                    linked = linked.replace(f"def {old}\n", f"def {new}\n")
                    break
        if linked not in program and (not scalar_only or linked not in (lean / "Cachepath/BuilderPortable.lean").read_text()):
            raise ValueError(f"unmatched SHAKE tree declaration on {target}: {linked}")
    checks = ["import Cachepath.BuilderShake", "open Aeneas Aeneas.Std Result slhdsa",
              "open slhdsa.cache.builder.nativeShake", "variable [b : Backend]"]
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    expected = {cut.removeprefix("crate::").replace("::", ".") for cut in cuts}
    for declaration in facade["common"]["declarations"](template):
        match = re.fullmatch(r"axiom (\S+)\s+(.*)", declaration, re.S)
        if not match or match[1] not in expected:
            raise ValueError(f"unexpected SHAKE builder external: {declaration}")
        symbol, signature = match.groups()
        expected.remove(symbol)
        binding = aliases.get(symbol, symbol)
        if symbol.endswith(".available"):
            binding += " N"
        checks.append(f"example {signature} := {binding}")
    if expected:
        raise ValueError(f"missing SHAKE builder externals: {expected}")
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input="\n".join(checks), text=True)


def check_parallel(target, scratch):
    root = facade["ROOT"]
    cuts = (*builder_cuts, "crate::cache::sha2_ops::build_leaves_parallel",
            "crate::cache::shake_ops::build_leaves_parallel", "crate::cache::shake_ops::fill_leaves_chunk",
            "crate::cache::shake_ops::simd::available", "crate::cache::shake_ops::simd::hash_pairs",
            "crate::cache::shake_ops::thash_pair")
    lib, dest = scratch / "parallel.llbc", scratch / "ParallelTree"
    facade["run"]([root / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
                   *(a for r in builders for a in ("--start-from", r)),
                   *(a for c in cuts for a in ("--opaque", c)),
                   "--dest-file", lib, "--", "--locked", "--features", "parallel,platform-sha2",
                   "--target", target], root / "rust")
    facade["run"]([root / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
                   "-no-progress-bar", "-split-files", "-dest", dest, lib], root)
    portable = lean.parent / "lean/Slhdsa"
    if set(decls(dest / "Types.lean", "slhdsa")) - set(decls(portable / "Types.lean", "slhdsa")):
        raise ValueError(f"unknown parallel tree type on {target}")
    sha2_program = set(decls(lean / "Cachepath/BuilderProgram.lean", "slhdsa"))
    shared = set(decls(portable / "Funs.lean", "slhdsa"))
    shake_program = (lean / "Cachepath/BuilderShakeProgram.lean").read_text()
    parallel_program = (lean / "Cachepath/BuilderParallelProgram.lean").read_text()
    for item in decls(dest / "Funs.lean", "slhdsa"):
        if item in shared:
            continue
        # The SHA-2 translation duplicates the reduction loop after the
        # two parallel branches. Check both copies against the proved body.
        loops = {"0": "1", "1": "0", "2": "1"}
        linked = re.sub(r"(cache\.sha2_ops\.build_xmss_tree_loop)([012])",
                        lambda m: m[1] + loops[m[2]], item)
        if linked in sha2_program:
            continue
        if "def cache.shake_ops.build_xmss_tree_loop" in linked:
            for old, new in (("cache.shake_ops.simd.available", "Backend.available"),
                             ("cache.shake_ops.simd.hash_pairs", "Backend.pairs"),
                             ("cache.shake_ops.thash_pair", "shake.hash.thash_pair"),
                             ("cache.shake_ops.", "")):
                linked = linked.replace(old, new)
            if linked not in shake_program:
                raise ValueError(f"changed parallel-feature SHAKE row loop on {target}")
            continue
        for family in ("sha2", "shake"):
            linked = linked.replace(f"def cache.{family}_ops.build_xmss_tree\n", f"def {family}Tree\n")
            linked = linked.replace(f"cache.{family}_ops.build_leaves_parallel", f"Pool.{family}")
        linked = linked.replace("cache.shake_ops.", "nativeShake.")
        if linked not in parallel_program:
            raise ValueError(f"unmatched parallel tree control flow on {target}: {linked}")


def main():
    facade["run"](["lake", "build", "Cachepath.BuiltSession", "Cachepath.BuilderPortable", "Cachepath.BuilderParallel"], lean)
    with tempfile.TemporaryDirectory() as directory:
        portable = "riscv64gc-unknown-none-elf"
        for target in (*facade["TARGETS"], portable):
            scratch = Path(directory) / target
            scratch.mkdir()
            check_constructor(target, scratch)
            check_builder(target, scratch)
            check_shake(target, scratch, scalar_only=target == portable)
            if target != portable:
                check_parallel(target, scratch)
            print(f"{target}: matched the public constructor and serial SHA-2 and SHAKE builders", flush=True)
    facade["audit_theorems"]("Cachepath.BuilderParallel", [
        "slhdsa.cache.builder.workers.sha2_kernel", "slhdsa.cache.builder.workers.shake_kernel",
        "CacheopsRust.Public.parallel_build_and_sign_many",
    ])
    facade["audit_theorems"]("Cachepath.BuilderPortable", [
        "slhdsa.cache.builder.nativeShake.portable_leaves_eq", "slhdsa.cache.builder.nativeShake.portable_level_eq",
    ])
    facade["audit_theorems"]("Cachepath.BuiltSession", [
        "CacheopsRust.cache.constructor.valid", "slhdsa.cache.builder.sha2_kernel",
        "slhdsa.cache.builder.nativeShake.kernel", "slhdsa.cache.builder.nativeShake.scalar_correct",
        "CacheopsRust.cache.constructor.reuse", "CacheopsRust.Public.build_and_sign",
        "CacheopsRust.Public.build_and_sign_many", "CacheopsRust.Public.scalar_build_and_sign_many",
    ])


if __name__ == "__main__":
    main()
