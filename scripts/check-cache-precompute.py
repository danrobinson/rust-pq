#!/usr/bin/env python3
"""Bind the exhaustive cache precomputation loop to the target Rust extractions."""
from pathlib import Path
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
entry = "crate::cache::TopTreeCache::precompute_layer_d2"
cuts = (*shared["builders"], "crate::util::block")


def linked(program):
    result = []
    shared_types = set(decls(lean / "Cacheops/Types.lean", "CacheopsRust"))
    if set(decls(program.with_name("Types.lean"), "slhdsa")) - shared_types:
        raise ValueError("unexpected precompute input types")
    shared_funs = set(decls(lean / "Cacheops/Funs.lean", "CacheopsRust"))
    public = (lean / "Cachepath/PublicProgram.lean").read_text()
    for body in decls(program, "slhdsa"):
        if "def cache.TopTreeCache.precompute_layer_d2" in body:
            body = body.replace("{N : Std.Usize}", "{N : Std.Usize} [b : Builders N]")
            for family in ("sha2", "shake"):
                body = body.replace(f"cache.{family}_ops.build_xmss_tree", f"b.{family}")
            result.append(body)
        elif body not in shared_funs and body not in public:
            raise ValueError("unmatched cache precompute dependency: " + body)
    if len(result) != 3:
        raise ValueError("expected a loop body, a loop, and the public precompute entry")
    return result


if __name__ == "__main__":
    expected = decls(lean / "Cachepath/PrecomputeProgram.lean", "CacheopsRust.Public")
    for target in (*facade["TARGETS"], "riscv64gc-unknown-none-elf"):
        with tempfile.TemporaryDirectory() as tmp:
            package = facade["extract"]("rust", target, "Precompute", Path(tmp), [entry], cuts)
            if linked(package / "Funs.lean") != expected:
                raise ValueError(f"precompute extraction changed on {target}")
            print(f"{target}: extracted cache precompute loop matches", flush=True)
    facade["run"](["lake", "build", "Cachepath.PlatformPortable"], lean)
    facade["audit_theorems"]("Cachepath.PlatformPortable", ["PortableSession.CacheopsRust.Public.scalar_keygen_sign_verify_with_precompute"])
    facade["audit_theorems"]("Cachepath.Precompute", ["CacheopsRust.Public.precompute_spec"])
