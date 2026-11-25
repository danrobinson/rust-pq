#!/usr/bin/env python3
"""Re-extract public cached signature construction and check FIPS 205 from caller inputs."""
from pathlib import Path
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
ROOT, LEAN = shared["ROOT"], shared["LEAN"]
OPS = ("sign_cached", "sign_deterministic_cached", "sign_cached_mut", "sign_deterministic_cached_mut")
SETS = tuple(f"{family}_{bits}{speed}" for family in ("sha2", "shake")
             for bits in (128, 192, 256) for speed in ("s", "f"))
STARTS = tuple("crate::cache::" + prefix + name
               for prefix in ("", *(s + "::" for s in SETS)) for name in OPS)
CUTS = tuple("crate::" + name for name in (
    "cache::sha2_ops::sign_from_digest", "cache::shake_ops::sign_from_digest",
    "cache::lookup_cached_index", "cache::tree_root", "shake256", "slh::message::randomizer",
    "slh::message::digest", "hash::h_msg", "hash::prf_msg", "cache::find_cached_index",
    "cache::sha2_ops::build_xmss_tree", "cache::shake_ops::build_xmss_tree",
))
EXTERNALS = {"cache.sha2_ops.sign_from_digest", "cache.shake_ops.sign_from_digest",
             "cache.lookup_cached_index", "shake256.Sponge.absorb",
             "shake256.Sponge.finish", "shake256.Sponge.new", "slh.message.randomizer",
             "slh.message.digest", "hash.h_msg", "hash.prf_msg", "alloc.vec.Vec.as_slice", "alloc.vec.Vec.remove",
             "alloc.vec.Vec.pop", "cache.find_cached_index", "cache.sha2_ops.build_xmss_tree",
             "cache.shake_ops.build_xmss_tree"}


def typed_check(native, source, scratch):
    """Compile the extracted 48 array-typed wrappers and prove each forwards to its FIPS entry."""
    std = shared["generated_declarations"](ROOT / "lean/Slhdsa/Funs.lean", "slhdsa")
    checked = {}
    code = ["import Cachepath.PublicMut", "open Aeneas Aeneas.Std Result ControlFlow Error",
            "namespace CacheopsRust.Public.Typed", "set_option linter.concreteInstances false",
            "set_option linter.unnecessarySeqFocus false", "set_option linter.unusedTactic false", "variable [backend : Closed.Backend]"]
    code.extend(f"abbrev width{n} := {n}#usize" for n in (16, 24, 32, 64, 96, 128))
    guards = ("cache.HashFamily.Insts.CoreCmpPartialEqHashFamily.eq", "cache.TopTreeCache.assert_family")
    for name in guards:
        checked[name] = native[name]
        code.append(source[name])
    code.append("""theorem guard {N : Usize} (c : CacheopsRust.cache.TopTreeCache N)
        (f : CacheopsRust.cache.HashFamily) (h : c.family = f) :
        cache.TopTreeCache.assert_family c f = ok () := by
      cases f <;> simp [cache.TopTreeCache.assert_family, cache.HashFamily.Insts.CoreCmpPartialEqHashFamily.eq,
                        h,bind_ok] <;> rfl""")
    # Debug formatting is reachable only on a failed assertion.
    for name in ("cache.HashFamily.Insts.CoreFmtDebug.fmt", "cache.HashFamily.Insts.CoreFmtDebug"):
        checked[name] = native[name]
    for param in SETS:
        family, bits = param.split("_")
        base = f"params.SHA2_{bits.upper()}"
        instance = f"sets.{param}.params.PARAMS"
        checked[base] = std[base]
        checked[instance] = std[instance]
        if family == "sha2":
            code.append(source[base])
        code.append(source[instance])
        n = int(bits[:3]) // 8
        for op in OPS:
            name = f"cache.{param}.{op}"
            body = source[name].replace("  cache.TopTreeCache.", "  CacheopsRust.Public.cache.TopTreeCache.")
            body = body.replace("CacheopsRust.Public.cache.TopTreeCache.assert_family",
                                "CacheopsRust.Public.Typed.cache.TopTreeCache.assert_family")
            body = body.replace("(cache.TopTreeCache ", "(CacheopsRust.cache.TopTreeCache ")
            body = body.replace("cache.HashFamily.", "CacheopsRust.cache.HashFamily.")
            if op.endswith("_mut"):
                body = body.replace("  (m :", f"  [Builders {n}#usize] (m :", 1)
            code.append(body)
            f = "Sha2" if family == "sha2" else "Shake"
            rng = "" if "deterministic" in op else f"(rnd : Array U8 width{n})"
            arg = "" if not rng else "rnd"
            b = f"[Builders width{n}]" if op.endswith("_mut") else ""
            code.append(f"""theorem {param}_{op}_eq {b} (m ctx : Slice U8)
                (sk : Array U8 width{4*n}) {rng} (c : CacheopsRust.cache.TopTreeCache width{n})
                (hf : c.family = .{f}) :
                {name} m ctx sk {arg} c =
                CacheopsRust.Public.cache.{op} {instance} m ctx sk.to_slice {arg} c := by
              simp only [{name}, guard c _ hf, bind_ok, lift] <;> rfl""")
            checked[name] = native[name]
    code.append("end CacheopsRust.Public.Typed")
    audit = scratch / "Typed.lean"
    audit.write_text("\n\n".join(code))
    shared["facade"]["run"](["lake", "env", "lean", audit], LEAN)
    return checked


def check(target, scratch, *, crate=None):
    output = shared["extract_target"](target, scratch, STARTS, CUTS, crate=crate)
    template = (output / "FunsExternal_Template.lean").read_text()
    actual = set(re.findall(r"(?m)^axiom ([^ :\n]+)", template))
    if actual != EXTERNALS:
        raise ValueError(f"unexpected public signer externals: {actual.symmetric_difference(EXTERNALS)}")
    parse = shared["generated_declarations"]
    checked = parse(LEAN / "Cacheops/Funs.lean", "CacheopsRust")
    program = "\n".join((LEAN / ("Cachepath/" + f + ".lean")).read_text()
                        for f in ("PublicProgram", "PublicMutProgram"))
    # The fully qualified names avoid a Lean ambiguity with the parameter 'cache'.
    program = program.replace("CacheopsRust.Public.cache.TopTreeCache.", "cache.TopTreeCache.")
    program = program.replace("[Builders N] ", "").replace("CacheopsRust.cache.TopTreeCache N", "cache.TopTreeCache N")
    local = {m[1]: " ".join(m[0].split()) for m in
             re.finditer(r"(?ms)^def (\S+)\n.*?(?=\n\n)", program)}
    checked.update(local)
    native = parse(output / "Funs.lean", "CacheopsRust", strict=True)
    raw = shared["facade"]["common"]
    source = {m[1]: item for item in raw["declarations"](raw["body"](output / "Funs.lean", "CacheopsRust"))
              if (m := re.search(r"\bdef\s+([\w.]+)", item))}
    mutation = runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))
    name = "cache.TopTreeCache.lookup_or_populate_d2"
    model = parse(LEAN / "Cachepath/MutationCaller.lean", "CacheopsRust")[name]
    model = model.replace(" (sha2 shake : cache.mutation.Builder N)", "")
    bindings = mutation["BINDINGS"]
    for old, new in bindings.items():
        model = re.sub(r"(?<![\w.])" + re.escape(new) + r"(?![\w.])", old, model)
    checked[name] = model
    for name in local:
        if name not in native:
            raise ValueError(f"missing public signer declaration {name}")
    # Detect a changed generic caller before instantiating its typed wrappers.
    for name in (*local, "cache.TopTreeCache.lookup_or_populate_d2"):
        if native[name] != checked[name]:
            raise ValueError(f"public signer declaration differs on {target}: {name}")
    checked.update(typed_check(native, source, scratch))
    for name, value in native.items():
        if value != checked.get(name):
            raise ValueError(f"public signer declaration differs on {target}: {name}")
    decls = shared["facade"]["common"]
    def types(path):
        return set(decls["declarations"](decls["body"](path, "CacheopsRust")))
    if types(output / "Types.lean") - types(LEAN / "Cacheops/Types.lean"):
        raise ValueError(f"public signer types differ on {target}")
    print(f"{target}: matched {len(native)} public signer declarations", flush=True)


def negative_control():
    """A cached caller that drops the context must fail the SHA-2 framing link."""
    with tempfile.TemporaryDirectory() as temp:
        scratch = Path(temp)
        crate = shared["copy_rust_crate"](scratch)
        file = crate / "src/cache.rs"
        source = file.read_text()
        good = "crate::slh::message::randomizer(sk_prf, addrnd, ctx, m)"
        if source.count(good) != 1:
            raise ValueError("could not locate the segmented cached randomizer call")
        file.write_text(source.replace(good, good.replace("ctx, m", "m, ctx")))
        try:
            check("aarch64-apple-darwin", scratch / "mutant", crate=crate)
        except ValueError as error:
            if str(error).endswith(": cache.sha2_ops.pure_digest"):
                print("Rejected swapped context and caller message in the public SHA-2 randomizer.")
                return
            raise
        raise ValueError("accepted a cached randomizer with swapped context and message")


if __name__ == "__main__":
    shared["facade"]["run"](["lake", "build", "Cachepath.PublicReuse"], LEAN)
    for target in (*shared["facade"]["TARGETS"], "riscv64gc-unknown-none-elf"):
        with tempfile.TemporaryDirectory() as tmp:
            check(target, Path(tmp))

    shared["facade"]["audit_theorems"]("Cachepath.PublicReuse", [
        "CacheopsRust.Public.runRequests_spec", "CacheopsRust.Public.new_then_sign_many",
        "CacheopsRust.Public.shake_digest_spec", "CacheopsRust.Public.sha2_digest_spec",
        "CacheopsRust.Public.sign_cached_mut_spec", "CacheopsRust.Public.sign_deterministic_cached_mut_spec",
        "CacheopsRust.Public.sign_cached_spec", "CacheopsRust.Public.sign_deterministic_cached_spec",
    ])
    negative_control()
