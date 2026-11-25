#!/usr/bin/env python3
"""Check the cache lifecycle and extracted SHA-2 and SHAKE serial signature assembly."""
from pathlib import Path
import os
import re
import runpy
import shutil
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
    "crate::cache::shake_ops::sign_from_digest",
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
    "crate::cache::shake_ops::fors_sign",
    "crate::cache::shake_ops::fors_pk_from_sig",
    "crate::cache::shake_ops::wots_sign",
    "crate::cache::shake_ops::xmss_node",
    "crate::cache::shake_ops::wots_pk_from_sig",
    "crate::shake256",
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
    "cache.shake_ops.fors_sign",
    "cache.shake_ops.fors_pk_from_sig",
    "cache.shake_ops.wots_sign",
    "cache.shake_ops.xmss_node",
    "cache.shake_ops.wots_pk_from_sig",
    "shake256.Sponge.new",
    "shake256.Sponge.absorb",
    "shake256.Sponge.finish",
}

FORBIDDEN = ("sorry", "admit", "axiom", "native_decide", "bv_decide")


def copy_rust_crate(destination):
    """Copy the crate inputs used by isolated negative-control extractions."""
    crate = destination / "rust"
    for name in ("src", "benches"):
        original = ROOT / "rust" / name
        if original.is_dir():
            shutil.copytree(original, crate / name)
    for name in ("Cargo.toml", "Cargo.lock"):
        shutil.copyfile(ROOT / "rust" / name, crate / name)
    return crate


def extract_target(target, scratch, starts=STARTS, opaques=OPAQUES, *, crate=None):
    dest = scratch / "Cacheops"
    dest.mkdir(parents=True)
    llbc = scratch / "cacheops.llbc"
    facade["run"](
        [
            CHARON,
            "cargo",
            "--preset=aeneas",
            *(arg for item in starts for arg in ("--start-from", item)),
            *(arg for item in opaques for arg in ("--opaque", item)),
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "platform-sha2",
            "--target",
            target,
        ],
        crate if crate is not None else ROOT / "rust",
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



# The scalar node and WOTS/FORS primitives below do not call architecture-specific
# code. After mapping the private Rust names, their complete Aeneas bodies are
# the same as those used by the portable FIPS proofs.
SCALAR_NAMES = {
    "start": "hash.start",
    "digest": "hash.digest",
    "thash": "hash.thash",
    "thash_pair": "hash.thash_pair",
    "wots_chain": "wots.chain",
    "wots_secret": "wots.secret",
    "fors_sk_gen": "fors.fors_sk_gen",
    "fors_node_portable": "fors.fors_node",
}


def generated_declarations(path, namespace, *, strict=False):
    parser = facade["common"]
    items = parser["declarations"](parser["body"](path, namespace))
    declarations = {}
    for item in items:
        match = re.search(r"\b(?:def|structure)\s+([\w.]+)", item)
        if not match:
            if strict:
                raise ValueError(f"unrecognized full signer declaration in {path}: {item[:120]}")
            continue
        declarations[match[1]] = " ".join(item.split())
    return declarations


SCALAR_CALLERS = ("wots_sign", "wots_pk_from_sig", "fors_sign", "fors_pk_from_sig")


def extract_scalar_callers(target, scratch, *, crate=None):
    prefix = "crate::cache::shake_ops::"
    cuts = ("simd::available", *("simd::" + name for name in SCALAR_CALLERS),
            "start", "digest", "thash", "wots_chain", "wots_secret", "fors_sk_gen",
            "fors_node_portable", "climb")
    return extract_target(target, scratch, tuple(prefix + name for name in (*SCALAR_CALLERS, "wots_pk_gen_portable")),
                          tuple(prefix + name for name in cuts) +
                          ("crate::wots::wots_digits", "crate::util::base_2b", "crate::util::block",
                           "crate::shake256"), crate=crate)


def scalar_caller_program(package):
    parser = facade["common"]
    items = parser["declarations"](parser["body"](package / "Funs.lean", "CacheopsRust"))
    return {m[1]: item for item in items
            if (m := re.search(r"\bdef (cache\.shake_ops\.[\w.]+)", item))}


def check_scalar_callers(package):
    source = (LEAN / "Cachepath/ShakeScalarProgram.lean").read_text()
    program = source.split("@[rust_loop_body]", 1)[1].rsplit("end slhdsa.CacheScalar", 1)[0]
    program = "@[rust_loop_body]" + program
    bodies = scalar_caller_program(package)

    def strip_line_ends(text):
        return "\n".join(line.rstrip() for line in text.strip().splitlines())

    if strip_line_ends("\n\n".join(bodies.values())) != strip_line_ends(program):
        raise ValueError("scalar cache WOTS/FORS program differs from the production extraction")

    portable = ROOT / "lean/Slhdsa"
    for file in ("Types.lean", "Funs.lean"):
        native = generated_declarations(package / file, "CacheopsRust")
        verified = generated_declarations(portable / file, "slhdsa")
        for name, body in native.items():
            if name not in bodies and verified.get(name) != body:
                raise ValueError(f"scalar cache dependency {name} differs from the portable declaration")


def check_node_dispatch(package, target):
    program = (LEAN / "Cachepath/ShakeNode.lean").read_text()
    start = program.index("def node (")
    end = program.index("\npartial_fixpoint", start) + len("\npartial_fixpoint")
    specialized = program[start:end].replace(
        "def node (available : Usize → Result Bool) (fast : FastNode) (leaf : LeafNode)",
        "def cache.shake_ops.xmss_node",
    )
    for parameter, rust in (("node available fast leaf", "xmss_node"),
                            ("available", "simd.available"), ("fast", "simd.xmss_node"),
                            ("leaf", "wots_pk_gen_portable")):
        specialized = re.sub(r"\b" + parameter + r"\b", "cache.shake_ops." + rust, specialized)
    generated = (package / "Funs.lean").read_text()
    begin = generated.index("def cache.shake_ops.xmss_node\n")
    end = generated.index("\npartial_fixpoint", begin) + len("\npartial_fixpoint")
    if generated[begin:end] != specialized:
        raise ValueError(f"cache recursive XMSS dispatch changed on {target}")


def extract_complete_signer(target, scratch, *, crate=None):
    """One root and no cuts inside the scalar SHAKE algorithms."""
    method = "crate::cache::shake_ops::"
    cuts = ("crate::cache::append_auth_path", "crate::cache::tree_root", "crate::shake256")
    accelerated = ("available", "xmss_node", *SCALAR_CALLERS)
    return extract_target(target, scratch, (method + "sign_from_digest",),
                          cuts + tuple(method + "simd::" + name for name in accelerated), crate=crate)


def linked_bodies(source):
    """Read the actual Lean declarations, preserving indentation and instruction order."""
    pattern = r"^(?:@\[rust_loop(?:_body)?\]\n)?def (cache\.shake_ops\.[\w.]+)\n[\s\S]*?(?=\n\n)"
    return {m[1]: m[0] for m in re.finditer(pattern, source, re.MULTILINE)}


def check_complete_signer(package, target):
    externals = set(re.findall(r"(?m)^axiom ([^ :\n]+)", (package / "FunsExternal_Template.lean").read_text()))
    methods = ("available", "xmss_node", *SCALAR_CALLERS)
    expected = {"cache.shake_ops.simd." + name for name in methods}
    expected.update(("cache.append_auth_path", "cache.tree_root", "shake256.Sponge.new",
                     "shake256.Sponge.absorb", "shake256.Sponge.finish"))
    types = re.findall(r"(?m)^axiom ([^ :\n]+)", (package / "TypesExternal_Template.lean").read_text())
    if externals != expected or types != ["shake256.Sponge"]:
        raise ValueError(f"unexpected full signer boundary on {target}: {externals}, {types}")

    # Check the linked entry point, its callers and both sets of iterator loops first.
    compiled = {}
    for module in ("ShakeScalarProgram", "ShakeClosedProgram"):
        compiled.update(linked_bodies((LEAN / f"Cachepath/{module}.lean").read_text()))
    native = scalar_caller_program(package)
    for name, verified in compiled.items():
        if [line.rstrip() for line in native[name].splitlines()] != verified.splitlines():
            raise ValueError(f"full signer {name} differs from the linked program on {target}")
    check_node_dispatch(package, target)
    linked = set(compiled) | {"cache.shake_ops.xmss_node"}

    # Account for every other generated body, including the shared parameters, address
    # layouts, scalar hash functions and cache accessors. The linker only renames private
    # hash helpers to their checked portable names.
    names = "|".join(sorted(SCALAR_NAMES, key=len, reverse=True))
    helpers = re.compile(r"cache\.shake_ops\.(" + names + r")(?=\b|_loop)")

    def portable_name(text):
        return helpers.sub(lambda m: "shake." + SCALAR_NAMES[m[1]], text)

    total = 0
    for file in ("Types.lean", "Funs.lean"):
        all_native = generated_declarations(package / file, "CacheopsRust", strict=True)
        assembly = generated_declarations(LEAN / "Cacheops" / file, "CacheopsRust")
        portable = generated_declarations(ROOT / "lean/Slhdsa" / file, "slhdsa")
        for name, declaration in all_native.items():
            if name in linked:
                continue
            if name != portable_name(name):
                if portable_name(declaration) != portable.get(portable_name(name)):
                    raise ValueError(f"full signer primitive {name} differs on {target}")
            elif declaration != assembly.get(name) and declaration != portable.get(name):
                raise ValueError(f"full signer dependency {name} has no matching verified body on {target}")
        total += len(all_native)
    return total

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
            if names != {"Types.lean", "Funs.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean"}:
                raise ValueError(f"unexpected Cacheops files on {target}: {names}")
            for file in ("Types.lean", "Funs.lean"):
                if (fresh / file).read_bytes() != (LEAN / "Cacheops" / file).read_bytes():
                    raise ValueError(f"Cacheops translation changed for {target}: {file}")
            types = set(re.findall(r"(?m)^axiom\s+([^\s:]+)\b",
                                   (fresh / "TypesExternal_Template.lean").read_text()))
            if types != {"shake256.Sponge"}:
                raise ValueError(f"unexpected Cacheops external types on {target}: {types}")
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
            complete = extract_complete_signer(target, scratch / "complete")
            count = check_complete_signer(complete, target)
            print(f"{target}: matched the complete scalar signer extraction ({count} declarations)", flush=True)

    run_symbolic_lifecycle_replay()

    audit_source_clean(
        [
            LEAN / "Cacheops/Types.lean",
            LEAN / "Cacheops/TypesExternal.lean",
            LEAN / "Cacheops/FunsExternal.lean",
            LEAN / "Cacheops/Funs.lean",
            LEAN / "Cachepath/EndToEnd.lean",
            LEAN / "Cachepath/ShakeEndToEnd.lean",
            LEAN / "Cachepath/ShakeClosedProgram.lean",
            LEAN / "Cachepath/ShakeClosed.lean",
            LEAN / "Cachepath/ShakeXmss.lean",
            LEAN / "Cachepath/ShakeNode.lean",
            LEAN / "Cachepath/ShakeScalar.lean",
            LEAN / "Cachepath/ShakeScalarProgram.lean",
        ]
    )

    facade["run"](["lake", "build", "Cachepath.ShakeClosed"], LEAN)
    facade["audit_theorems"](
        "Cachepath.ShakeClosed",
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
            "CacheopsRust.Closed.sign_from_digest_eq",
            "CacheopsRust.Closed.sign_from_digest_with_cache_spec",
            "CacheopsRust.ShakeNode.node_eq",
            "CacheopsRust.ShakeNode.scalar_node_eq",
            "slhdsa.CacheScalar.wots_pk_gen_eq",
            "slhdsa.cache.endtoend.shake.climb_eq",
            "slhdsa.CacheScalar.assembly_contracts",
            "slhdsa.CacheScalar.wots_sign_eq",
            "slhdsa.CacheScalar.wots_recover_eq",
            "slhdsa.CacheScalar.fors_sign_eq",
            "slhdsa.CacheScalar.fors_recover_eq",
            "slhdsa.cache.endtoend.shake.thash_pair_eq",
            "slhdsa.cache.endtoend.shake.xmss_sign_eq",
            "slhdsa.cache.endtoend.shake.xmss_pk_from_sig_eq",
            "slhdsa.cache.endtoend.shake.sign_from_digest_spec",
            "slhdsa.cache.endtoend.shake.sign_from_digest_with_cache_spec",
            "slhdsa.cache.endtoend.cached_htSign_eq_fips",
            "slhdsa.cache.endtoend.cached_sign_eq_fips",
            "slhdsa.cache.endtoend.cached_hash_slh_sign_prehashed_eq_fips",
            "slhdsa.cache.endtoend.cached_hash_slh_sign_eq_fips",
            "slhdsa.cache.endtoend.all_12_parameter_sets_valid",
        ],
    )
    print("SHA-2 and SHAKE cache assembly proofs, lifecycle replay, and axiom audits PASSED!", flush=True)


if __name__ == "__main__":
    main()
