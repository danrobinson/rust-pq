#!/usr/bin/env python3
"""Re-extract the mutable d-2 cache policy and check its Lean safety theorem."""
from pathlib import Path
import re
import runpy
import tempfile

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
common = facade["common"]
lean = facade["LEAN"]
ROOT = "crate::cache::TopTreeCache::lookup_or_populate_d2"
CUTS = tuple("crate::cache::" + fn for fn in (
    "find_cached_index", "sha2_ops::build_xmss_tree", "shake_ops::build_xmss_tree",
))
BINDINGS = {
    "cache.find_cached_index": "cache.mutation.find",
    "alloc.vec.Vec.remove": "cache.mutation.remove",
    "alloc.vec.Vec.pop": "cache.mutation.pop",
    "alloc.vec.Vec.insert": "cache.mutation.insert",
    "cache.sha2_ops.build_xmss_tree": "sha2",
    "cache.shake_ops.build_xmss_tree": "shake",
}


def decls(path, namespace):
    return list(common["declarations"](common["body"](path, namespace)))


def check_target(target, scratch):
    package = facade["extract"]("rust", target, "Policy", scratch, [ROOT], CUTS)
    nominal = decls(package / "Types.lean", "slhdsa")
    shared = decls(lean / "Cacheops/Types.lean", "CacheopsRust")
    if len(nominal) != 4 or set(nominal) - set(shared):
        raise ValueError(f"unmatched cache structures on {target}")

    (caller,) = decls(package / "Funs.lean", "slhdsa")
    caller = caller.replace("{N : Std.Usize}", "{N : Std.Usize} (sha2 shake : cache.mutation.Builder N)")
    for old, new in BINDINGS.items():
        if old not in caller:
            raise ValueError(f"missing call to {old} on {target}")
        caller = caller.replace(old, new)
    if [caller] != decls(lean / "Cachepath/MutationCaller.lean", "CacheopsRust"):
        raise ValueError(f"extracted mutation control flow changed on {target}")

    # Ask Lean to check the exact fresh external signatures, including binder
    # order and all element types, against the modeled standard library and
    # extracted search. The two tree builders remain parameters to the theorem.
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    seen = set()
    checks = ["import Cachepath.Mutation", "open Aeneas Aeneas.Std Result CacheopsRust"]
    for block in common["declarations"](template):
        match = re.fullmatch(r"(?:@\[.*?\]\s*)?axiom\s+(\S+)\s+(.*)", block, re.S)
        if not match or match[1] not in BINDINGS:
            raise ValueError(f"unexpected external declaration on {target}: {block}")
        name, sig = match.groups()
        seen.add(name)
        if name.endswith("build_xmss_tree"):
            checks.append("example " + sig.replace("{N : Std.Usize}", "{N : Std.Usize} (b : cache.mutation.Builder N)") + " := b")
        elif name.startswith("alloc.vec."):
            checks.append(f"example {sig} := {BINDINGS[name]} A")
        else:
            checks.append(f"example {sig} := {BINDINGS[name]}")
    if seen != BINDINGS.keys() - {"alloc.vec.Vec.insert"}:
        raise ValueError(f"unexpected external call set on {target}")
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input="\n".join(checks), text=True)
    print(f"{target}: mutable d-2 cache extraction and external signatures matched", flush=True)


def main():
    facade["run"](["lake", "build", "Cachepath.Mutation"], lean)
    with tempfile.TemporaryDirectory() as directory:
        for target in facade["TARGETS"]:
            scratch = Path(directory) / target
            scratch.mkdir()
            check_target(target, scratch)
    facade["audit_theorems"]("Cachepath.Mutation", ["CacheopsRust.cache.mutation.lookup_or_populate_safe"])


if __name__ == "__main__":
    main()
