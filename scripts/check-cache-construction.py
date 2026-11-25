#!/usr/bin/env python3
"""Compare the public cache constructor and SHA-2 tree builder with fresh Aeneas output."""
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


def main():
    facade["run"](["lake", "build", "Cachepath.BuilderSha2"], lean)
    with tempfile.TemporaryDirectory() as directory:
        for target in facade["TARGETS"]:
            scratch = Path(directory) / target
            scratch.mkdir()
            check_constructor(target, scratch)
            check_builder(target, scratch)
            print(f"{target}: matched the public constructor and serial SHA-2 builder", flush=True)
    facade["audit_theorems"]("Cachepath.BuilderSha2", [
        "CacheopsRust.cache.constructor.valid", "slhdsa.cache.builder.sha2_kernel",
    ])


if __name__ == "__main__":
    main()
