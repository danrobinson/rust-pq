#!/usr/bin/env python3
"""Re-extract public cached signature construction and check FIPS 205 from caller inputs."""
from pathlib import Path
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
ROOT, LEAN = shared["ROOT"], shared["LEAN"]
STARTS = tuple("crate::cache::" + name for name in ("sign_cached", "sign_deterministic_cached"))
CUTS = tuple("crate::" + name for name in (
    "cache::sha2_ops::sign_from_digest", "cache::shake_ops::sign_from_digest",
    "cache::lookup_cached_index", "cache::tree_root", "shake256", "slh::message::randomizer",
    "slh::message::digest", "hash::h_msg", "hash::prf_msg",
))
EXTERNALS = {"cache.sha2_ops.sign_from_digest", "cache.shake_ops.sign_from_digest",
             "cache.lookup_cached_index", "shake256.Sponge.absorb",
             "shake256.Sponge.finish", "shake256.Sponge.new", "slh.message.randomizer",
             "slh.message.digest", "hash.h_msg", "hash.prf_msg", "alloc.vec.Vec.as_slice"}


def check(target, scratch, *, crate=None):
    output = shared["extract_target"](target, scratch, STARTS, CUTS, crate=crate)
    template = (output / "FunsExternal_Template.lean").read_text()
    actual = set(re.findall(r"(?m)^axiom ([^ :\n]+)", template))
    if actual != EXTERNALS:
        raise ValueError(f"unexpected public signer externals: {actual.symmetric_difference(EXTERNALS)}")
    parse = shared["generated_declarations"]
    checked = parse(LEAN / "Cacheops/Funs.lean", "CacheopsRust")
    program = (LEAN / "Cachepath/PublicProgram.lean").read_text()
    # The fully qualified names avoid a Lean ambiguity with the parameter 'cache'.
    program = program.replace("CacheopsRust.Public.cache.TopTreeCache.", "cache.TopTreeCache.")
    local = {m[1]: " ".join(m[0].split()) for m in
             re.finditer(r"(?ms)^def (\S+)\n.*?(?=\n\n)", program)}
    checked.update(local)
    native = parse(output / "Funs.lean", "CacheopsRust", strict=True)
    for name in local:
        if name not in native:
            raise ValueError(f"missing public signer declaration {name}")
    for name, value in native.items():
        if value != checked.get(name):
            raise ValueError(f"public signer declaration differs on {target}: {name}")
    types = parse(output / "Types.lean", "CacheopsRust")
    known = parse(LEAN / "Cacheops/Types.lean", "CacheopsRust")
    if any(value != known.get(name) for name, value in types.items()):
        raise ValueError(f"public signer types differ on {target}")
    print(f"{target}: matched {len(native)} public signer declarations", flush=True)


if __name__ == "__main__":
    for target in shared["facade"]["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            check(target, Path(tmp))
    shared["facade"]["run"](["lake", "build", "Cachepath.Public"], LEAN)
    shared["facade"]["audit_theorems"]("Cachepath.Public", [
        "CacheopsRust.Public.shake_digest_spec", "CacheopsRust.Public.sha2_digest_spec",
        "CacheopsRust.Public.sign_cached_spec", "CacheopsRust.Public.sign_deterministic_cached_spec",
    ])
