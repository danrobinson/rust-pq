#!/usr/bin/env python3
"""Check cache key-association, reuse/eviction/insertion, and end-to-end cached signing proofs."""
from pathlib import Path
import os
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
ROOT = facade["ROOT"]
LEAN = facade["LEAN"]
CHARON = ROOT / ".tools/aeneas/charon/bin/charon"
AENEAS = ROOT / ".tools/aeneas/bin/aeneas"

STARTS = (
    "crate::cache::digest_tree",
    "crate::cache::digest_leaf",
    "crate::cache::TopTreeCache::pk_root",
    "crate::cache::TopTreeCache::matches_key",
    "crate::cache::TopTreeCache::set_layer_d2_capacity",
    "crate::cache::TopTreeCache::with_layer_d2_capacity",
    "crate::cache::TopTreeCache::layer_d2_tree_index",
    "crate::cache::TopTreeCache::lookup_d2",
    "crate::cache::sha2_ops::sign_from_digest",
)

OPAQUES = (
    "crate::cache::append_auth_path",
    "crate::cache::tree_root",
    "crate::cache::lookup_cached_index",
    "crate::hash::seed_ctx",
    "crate::wots::wots_sign",
    "crate::xmss::xmss_sign",
    "crate::xmss::xmss_pk_from_sig",
    "crate::fors::fors_sign",
    "crate::fors::fors_pk_from_sig",
)

EXPECTED_EXTERNALS = {
    "alloc.vec.Vec.truncate",
    "alloc.vec.Vec.as_slice",
    "cache.append_auth_path",
    "cache.tree_root",
    "cache.lookup_cached_index",
    "xmss.xmss_pk_from_sig",
    "xmss.xmss_sign",
    "wots.wots_sign",
    "hash.seed_ctx",
    "fors.fors_pk_from_sig",
    "fors.fors_sign",
}

FORBIDDEN = ("sorry", "admit", "axiom", "native_decide", "bv_decide")


def extract_target(target, scratch):
    dest = scratch / "Cacheops"
    dest.mkdir(parents=True)
    llbc = scratch / "cacheops.llbc"
    facade["run"](
        [
            CHARON,
            "cargo",
            "--preset=aeneas",
            *(arg for item in STARTS for arg in ("--start-from", item)),
            *(arg for item in OPAQUES for arg in ("--opaque", item)),
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "platform-sha2",
            "--target",
            target,
        ],
        ROOT / "rust",
    )
    facade["run"](
        [
            AENEAS,
            "-backend",
            "lean",
            "-abort-on-error",
            "-no-progress-bar",
            "-split-files",
            "-namespace",
            "CacheopsRust",
            "-dest",
            dest,
            llbc,
        ],
        ROOT,
    )
    return dest


def slice_block(source, header):
    start = source.index(header)
    end = source.index("\n}\n", start)
    return source[start : end + 3]


def run_symbolic_lifecycle_replay():
    cache_rs = (ROOT / "rust/src/cache.rs").read_text()
    items = [
        slice_block(cache_rs, "#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum HashFamily {"),
        slice_block(cache_rs, "#[derive(Clone, Debug, PartialEq, Eq)]\nstruct LayerD2Entry<const N: usize> {"),
        slice_block(cache_rs, "fn find_cached_index<const N: usize>"),
        slice_block(cache_rs, "#[derive(Clone, Debug, PartialEq, Eq)]\npub struct TopTreeCache<const N: usize> {"),
        slice_block(cache_rs, "fn tree_node_count(hp: u32) -> usize {"),
        slice_block(cache_rs, "fn tree_root<const N: usize>"),
        slice_block(cache_rs, "fn digest_tree(p: &Params, digest: &[u8]) -> u64 {"),
        slice_block(cache_rs, "fn digest_leaf(p: &Params, digest: &[u8]) -> u32 {"),
        slice_block(cache_rs, "impl<const N: usize> TopTreeCache<N> {"),
        slice_block(cache_rs, "pub fn keygen_with_cache<const N: usize>("),
        slice_block(cache_rs, "fn lookup_cached_index<const N: usize>"),
    ]
    harness = (HERE / "cache-proof/lifecycle.rs").read_text().replace(
        "// PRODUCTION_CACHE_ITEMS", "\n\n".join(items)
    )
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "lifecycle.rs"
        exe = Path(tmp) / "lifecycle"
        src.write_text(harness)
        subprocess.run(
            [
                "rustc",
                "--edition=2021",
                "-Awarnings",
                "-O",
                "-C",
                "overflow-checks=yes",
                src,
                "-o",
                exe,
            ],
            check=True,
        )
        subprocess.run([exe], check=True)
    print("Symbolic cache reuse/insertion/eviction/end-to-end replay PASSED (all 12 parameter sets)", flush=True)


def audit_source_clean(paths):
    for path in paths:
        text = path.read_text()
        for tok in FORBIDDEN:
            if re.search(rf"\b{tok}\b", text):
                raise ValueError(f"forbidden token '{tok}' in {path}")


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".elan/bin"),
            str(Path.home() / ".cargo/bin"),
            os.environ["PATH"],
        ]
    )

    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"]:
            scratch = Path(tmp) / target
            scratch.mkdir()
            fresh = extract_target(target, scratch)
            names = {p.name for p in fresh.iterdir()}
            if names != {"Types.lean", "Funs.lean", "FunsExternal_Template.lean"}:
                raise ValueError(f"unexpected Cacheops files on {target}: {names}")
            for file in ("Types.lean", "Funs.lean"):
                if (fresh / file).read_bytes() != (LEAN / "Cacheops" / file).read_bytes():
                    raise ValueError(f"Cacheops translation changed for {target}: {file}")
            found = set(
                re.findall(
                    r"(?m)^axiom\s+([^\s:]+)\b",
                    (fresh / "FunsExternal_Template.lean").read_text(),
                )
            )
            if found != EXPECTED_EXTERNALS:
                raise ValueError(
                    f"unexpected Cacheops externals on {target}: {found} != {EXPECTED_EXTERNALS}"
                )
            print(f"{target}: Cacheops translation matched byte-for-byte", flush=True)

    run_symbolic_lifecycle_replay()

    audit_source_clean(
        [
            LEAN / "Cacheops/Types.lean",
            LEAN / "Cacheops/FunsExternal.lean",
            LEAN / "Cacheops/Funs.lean",
            LEAN / "Cachepath/EndToEnd.lean",
        ]
    )

    facade["run"](["lake", "build", "Cachepath.EndToEnd"], LEAN)
    facade["audit_theorems"](
        "Cachepath.EndToEnd",
        [
            "slhdsa.cache.endtoend.top_root_eq_fips",
            "slhdsa.cache.endtoend.pk_root_spec",
            "slhdsa.cache.endtoend.pk_root_eq_fips",
            "slhdsa.cache.endtoend.matches_key_spec",
            "slhdsa.cache.endtoend.matches_key_iff_pk_eq",
            "slhdsa.cache.endtoend.matches_key_valid_key",
            "slhdsa.cache.endtoend.lookup_hit_built",
            "slhdsa.cache.endtoend.lookup_d2_spec",
            "slhdsa.cache.endtoend.set_capacity_preserves_valid",
            "slhdsa.cache.endtoend.with_capacity_preserves_valid",
            "slhdsa.cache.endtoend.evict_preserves_valid",
            "slhdsa.cache.endtoend.move_to_front_preserves_valid",
            "slhdsa.cache.endtoend.insert_preserves_valid",
            "slhdsa.cache.endtoend.precompute_d2_preserves_valid",
            "slhdsa.cache.endtoend.cache_digest_tree_spec",
            "slhdsa.cache.endtoend.cache_digest_leaf_spec",
            "slhdsa.cache.endtoend.layer_d2_tree_index_spec",
            "slhdsa.cache.endtoend.sign_from_digest_spec",
            "slhdsa.cache.endtoend.sign_from_digest_with_cache_spec",
            "slhdsa.cache.endtoend.cached_htSign_eq_fips",
            "slhdsa.cache.endtoend.cached_sign_eq_fips",
            "slhdsa.cache.endtoend.cached_hash_slh_sign_prehashed_eq_fips",
            "slhdsa.cache.endtoend.cached_hash_slh_sign_eq_fips",
            "slhdsa.cache.endtoend.all_12_parameter_sets_valid",
        ],
    )
    print("ALL Cachepath.EndToEnd checks, lifecycle replay, and axiom audits PASSED!", flush=True)


if __name__ == "__main__":
    main()
