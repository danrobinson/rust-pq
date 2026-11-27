#!/usr/bin/env python3
"""Bind the feature-parametric native cache session to both AArch64 Rust callers."""
import os
from pathlib import Path
import re
import runpy
import tempfile

cache = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
facade = cache["facade"]
lean = cache["LEAN"]


def compare(package):
    for name in ("Types.lean", "Funs.lean"):
        if (package / name).read_bytes() != (lean / "Cacheops" / name).read_bytes():
            raise ValueError(f"fresh cached caller differs in {name}")
    external = (package / "FunsExternal_Template.lean").read_text()
    if set(re.findall(r"(?m)^axiom\s+([^\s:]+)\b", external)) != cache["EXPECTED_EXTERNALS"]:
        raise ValueError("unexpected external cached-call cut")


def audit():
    roots = ("slhdsa.CachedArm.sign_from_digest_spec",
             "slhdsa.CachedArm.sign_from_digest_with_cache_spec",
             "slhdsa.CachedArm.keygen_sign_stream",
             *("ArmCachedApi.CacheopsRust.Public." + name for name in
               ("sign_cached_spec", "sign_deterministic_cached_spec",
                "sign_cached_mut_spec", "sign_deterministic_cached_mut_spec")))
    roundtrip = "slhdsa.CachedArm.seeded_roundtrip"
    facade["audit_theorems"]("Armwide.CachedReachability", [roundtrip, "LinuxNativeCacheRoundTrip." + roundtrip])
    joined = "ArmCachedParallel.CacheopsRust.cache.parallelSign.sha2_joined"
    facade["audit_theorems"]("Armwide.CachedReachability",
                             [*roots, *("LinuxNativeCache." + r for r in roots),
                              joined, "LinuxNativeCacheParallel." + joined])


def main():
    os.environ["PATH"] = os.pathsep.join((str(Path.home()/".elan/bin"),
                                          str(Path.home()/".cargo/bin"), os.environ["PATH"]))
    facade["run"](["lake", "build", "Armwide.CachedReachability"], lean)
    audit()
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for target in facade["TARGETS"][:2]:
            destination = root / target
            destination.mkdir()
            compare(cache["extract_target"](target, destination))
            print(f"{target}: complete cached caller and external cut matched", flush=True)
        mutation = root / "mutated"
        mutation.mkdir()
        crate = cache["copy_rust_crate"](mutation)
        source = crate / "src/cache.rs"
        text = source.read_text()
        tag = ".with_type(FORS_TREE)"
        if tag not in text:
            raise ValueError("cached FORS address mutation site changed")
        source.write_text(text.replace(tag, ".with_type(WOTS_HASH)", 1))
        package = cache["extract_target"](facade["TARGETS"][0], mutation, crate=crate)
        # Check specifically the domain value in the live digest entry. A source
        # location or unrelated function difference must not pass this control.
        name = "cache.sha2_ops.sign_from_digest"
        declaration = cache["generated_declarations"]
        fresh = declaration(package / "Funs.lean", "CacheopsRust")[name]
        original = declaration(lean / "Cacheops/Funs.lean", "CacheopsRust")[name]
        if fresh == original or fresh.replace("address.WOTS_HASH", "address.FORS_TREE") != original:
            raise ValueError("could not isolate FORS domain in mutated live cached signer")
        print("changing the cached FORS domain changed its extracted entry", flush=True)


if __name__ == "__main__":
    main()
