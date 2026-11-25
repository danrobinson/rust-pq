#!/usr/bin/env python3
"""Replay Rust keygen_with_cache and audit its composition with repeated cached signing."""
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import tempfile

construction = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = construction["facade"], construction["decls"], construction["lean"]


def linked_caller(target, scratch, crate="rust"):
    cuts = construction["constructor_cuts"]
    package = facade["extract"](crate, target, "Keygen", scratch, ["crate::cache::keygen_with_cache"], cuts)
    if set(decls(package / "Types.lean", "slhdsa")) - set(decls(lean / "Cacheops/Types.lean", "CacheopsRust")):
        raise ValueError(f"unexpected keygen type on {target}")
    (caller,) = decls(package / "Funs.lean", "slhdsa")
    caller = caller.replace("def cache.keygen_with_cache", "def keygen")
    caller = caller.replace("(N : Std.Usize) (family", "(N : Std.Usize) (sha2 shake : cache.mutation.Builder N) (family")
    for family in ("sha2", "shake"):
        caller = caller.replace(f"cache.{family}_ops.build_xmss_tree", family)
    return caller, package


def replay(target, scratch):
    caller, package = linked_caller(target, scratch)
    cuts = construction["constructor_cuts"]
    if [caller] != decls(lean / "Cachepath/KeygenProgram.lean", "CacheopsRust.cache.generatedKeys"):
        raise ValueError(f"keygen_with_cache differs from the proved caller on {target}")
    checks = ["import Cachepath.Keygen", "open Aeneas Aeneas.Std Result CacheopsRust"]
    expected = {cut.removeprefix("crate::").replace("::", ".") for cut in cuts}
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    for external in facade["common"]["declarations"](template):
        name, signature = re.fullmatch(r"axiom (\S+)\s+(.*)", external, re.S).groups()
        expected.remove(name)
        if name.endswith(".build_xmss_tree"):
            signature = signature.replace("{N : Std.Usize}", "{N : Std.Usize} (builder : cache.mutation.Builder N)")
            binding = "builder"
        else:
            binding = "@" + name + " N"
        checks.append(f"example {signature} := {binding}")
    if expected:
        raise ValueError(f"unmatched keygen externals on {target}: {expected}")
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input="\n".join(checks), text=True)


def check_typed(target, scratch):
    """Compile 24 named wrappers and round-trip the array outputs of each typed key generator."""
    suites = [(family, bits, speed) for family in ("sha2", "shake")
              for bits in (128, 192, 256) for speed in ("s", "f")]
    roots = [f"crate::cache::{family}_{bits}{speed}::{op}" for family, bits, speed in suites
             for op in ("new", "keygen_with_cache")]
    package = facade["extract"]("rust", target, "TypedKeys", scratch, roots,
                                ("crate::cache::keygen_with_cache", *construction["constructor_cuts"]))
    if set(decls(package / "Types.lean", "slhdsa")) - set(decls(lean / "Cacheops/Types.lean", "CacheopsRust")):
        raise ValueError(f"changed typed cache input types on {target}")
    source = {re.search(r"(?m)^def (\S+)", item)[1]: item for item in decls(package / "Funs.lean", "slhdsa")}
    reference = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    # The very same constructor body appears in its standalone extraction.
    constructor = source.pop("cache.TopTreeCache.new")
    constructor = constructor.replace("def cache.TopTreeCache.new", "def newCache").replace(
        "(N : Std.Usize) (family", "(N : Std.Usize) (sha2 shake : cache.mutation.Builder N) (family")
    for family in ("sha2", "shake"):
        constructor = constructor.replace(f"cache.{family}_ops.build_xmss_tree", family)
    if [constructor] != decls(lean / "Cachepath/ConstructorProgram.lean", "CacheopsRust.cache.constructor"):
        raise ValueError(f"typed facade has a different generic cache constructor on {target}")
    code = ["""import Cachepath.PlatformPortable
open Aeneas Aeneas.Std Result
namespace CacheopsRust.TypedKeys
noncomputable section
local instance : slhdsa.cache.builder.nativeShake.Backend := slhdsa.cache.builder.nativeShake.scalar
abbrev sha2 {N : Usize} : cache.mutation.Builder N := PortableSession.slhdsa.cache.sha2_ops.build_xmss_tree
abbrev shake {N : Usize} : cache.mutation.Builder N := PortableSession.slhdsa.cache.builder.nativeShake.build_xmss_tree
abbrev cache.TopTreeCache.new (N : Usize) := CacheopsRust.cache.constructor.newCache N sha2 shake
abbrev cache.keygen_with_cache (N : Usize) := CacheopsRust.cache.generatedKeys.keygen N sha2 shake

theorem produces {N : Usize} (p : params.Params) (hp : slhdsa.PN (toSlhParams p) N) (f : cache.HashFamily)
    (seed sk pk : Slice U8) (hs : seed.length = 3*N.val) (hk : sk.length = 4*N.val) (hp' : pk.length = 2*N.val) :
    cache.keygen_with_cache N f p seed sk pk ⦃ out =>
      CacheopsRust.cache.generatedKeys.Generated (Public.familyParams p f) f seed out ⦄ := by
  apply CacheopsRust.cache.generatedKeys.keygen_spec _ _ _ _ _ hp.n_eq.symm
  · cases f <;> exact hp.n
  · cases f <;> rfl
  · cases f <;> rfl
  · exact Public.familyParams_valid _ hp _
  · rintro rfl; exact PortableSession.slhdsa.cache.builder.sha2_kernel _ hp
  · rintro rfl; exact PortableSession.slhdsa.cache.builder.nativeShake.kernel
        (slhdsa.cache.builder.nativeShake.scalar_correct N) _ hp
  all_goals assumption

theorem copy_back {n : Usize} (a : Array U8 n) (s : Slice U8) (sz : s.length = n.val) :
    (Array.from_slice a s).to_slice = s := by
  apply Slice.ext
  simpa only [Array.val_to_slice] using Array.from_slice_val a s sz
"""]
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    externals = dict(re.fullmatch(r"axiom (\S+)\s+(.*)", item, re.S).groups()
                     for item in facade["common"]["declarations"](template))
    signature = externals.pop("cache.keygen_with_cache")
    expected = {cut.removeprefix("crate::").replace("::", ".") for cut in construction["constructor_cuts"]}
    if set(externals) != expected:
        raise ValueError(f"changed typed constructor externals on {target}: {set(externals) ^ expected}")
    code.append(f"example {signature} := cache.keygen_with_cache N")
    for family, bits, speed in suites:
        name = f"{family}_{bits}{speed}"
        n = bits // 8
        tag = "Sha2" if family == "sha2" else "Shake"
        param = f"sets.{name}.params.PARAMS"
        constants = ([f"params.SHA2_{bits}{speed.upper()}"] if family == "sha2" else []) + [param]
        for constant in constants:
            definition = source.pop(constant)
            if definition not in reference:
                raise ValueError(f"typed constructor references a changed {constant}")
            code.append(definition)
        constructor = f"cache.{name}.new"
        keygen = f"cache.{name}.keygen_with_cache"
        code.extend([source.pop(constructor), source.pop(keygen)])
        code.append(f"""theorem {name}_new (sk : Array U8 {4*n}#usize) :
            {constructor} sk = CacheopsRust.cache.constructor.newCache {n}#usize sha2 shake .{tag} {param} sk.to_slice := by
              simp only [{constructor},lift,bind_ok,cache.TopTreeCache.new]

          theorem {name}_keygen_eq (seeds : Array U8 {3*n}#usize) (sk : Array U8 {4*n}#usize)
              (pk : Array U8 {2*n}#usize) :
              {keygen} seeds sk pk = (do
                let (c,secret,pub) ← CacheopsRust.cache.generatedKeys.keygen {n}#usize sha2 shake .{tag} {param}
                  seeds.to_slice sk.to_slice pk.to_slice
                ok (c,Array.from_slice sk secret,Array.from_slice pk pub)) := by
            simp only [{keygen},Array.to_slice_mut,lift,bind_ok,uncurry,cache.keygen_with_cache]

          theorem {name}_roundtrip (seeds : Array U8 {3*n}#usize) (sk : Array U8 {4*n}#usize)
            (pk : Array U8 {2*n}#usize) (m ctx : Slice U8) (rnd : Array U8 {n}#usize) (short : ctx.length ≤ 255)
            (room : slhdsa.Room m.length (slhdsa.msgSlack {n}+257)) :
            (do let (c,secret,pub) ← {keygen} seeds sk pk
                let sig ← @PortableSession.CacheopsRust.Public.cache.sign_cached CacheopsRust.Closed.scalar {n}#usize
                  {param} m ctx secret.to_slice rnd c
                match sig with
                | none => ok false
                | some s => @CacheopsRust.Public.verifyGenerated {n}#usize .{tag} (toSlhParams {param}) m s.deref ctx pub.to_slice) =
              ok true := by
            have pn : slhdsa.PN (toSlhParams {param}) {n}#usize := by with_unfolding_all exact slhdsa.sha2_{bits}{speed}.pn
            have hs : seeds.to_slice.length = 3*({n}#usize).val := by simp [Slice.length]
            have hk : sk.to_slice.length = 4*({n}#usize).val := by simp [Slice.length]
            have hp : pk.to_slice.length = 2*({n}#usize).val := by simp [Slice.length]
            obtain ⟨⟨c,secret,pub⟩,run,g⟩ := slhdsa.spec_imp_exists (produces {param} pn .{tag}
              seeds.to_slice sk.to_slice pk.to_slice hs hk hp)
            have roundtrip := PortableSession.CacheopsRust.Public.scalar_keygen_sign_verify {param} pn .{tag}
              seeds.to_slice sk.to_slice pk.to_slice m ctx rnd hs hk hp short room
            change CacheopsRust.cache.generatedKeys.keygen _ sha2 shake _ _ _ _ _ = _ at run
            simp only [run,bind_ok,uncurry] at roundtrip
            change cache.keygen_with_cache _ _ _ _ _ _ = _ at run
            have key : secret.length = ({4*n}#usize).val := g.secretLength
            have publicKey : pub.length = ({2*n}#usize).val := g.publicLength
            simp only [{keygen},Array.to_slice_mut,lift,bind_ok,uncurry,run,copy_back sk secret key,
              copy_back pk pub publicKey]
            apply Eq.trans _ roundtrip
            congr 1""")
    if source:
        raise ValueError(f"unexpected typed key declarations on {target}: {source.keys()}")
    code.extend(["end", "end CacheopsRust.TypedKeys"])
    audit = scratch / "TypedKeygen.lean"
    audit.write_text("\n\n".join(code))
    facade["run"](["lake", "env", "lean", audit], lean)


def reject_wrong_seed(scratch):
    """A type-correct wrong write to SK.PKseed must invalidate the postcondition proof."""
    old = "sk[2 * N..3 * N].copy_from_slice(&pk_seed);"
    new = "sk[2 * N..3 * N].copy_from_slice(&sk_prf);"
    endtoend = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
    crate = endtoend["copy_rust_crate"](scratch)
    cache = crate / "src/cache.rs"
    original = cache.read_text()
    if original.count(old) != 1:
        raise ValueError("expected one generated secret key public seed write")
    cache.write_text(original.replace(old, new))
    caller, _ = linked_caller("aarch64-apple-darwin", scratch, crate)
    program = lean / "Cachepath/KeygenProgram.lean"
    (proved,) = decls(program, "CacheopsRust.cache.generatedKeys")
    if caller == proved:
        raise ValueError("wrong seed write still matches proved caller")
    modules = scratch / "Cachepath"
    shutil.copytree(lean / ".lake/build/lib/lean/Cachepath", modules)
    source = modules / "KeygenProgram.lean"
    source.write_text(program.read_text().split("def keygen", 1)[0] + caller + "\nend CacheopsRust.cache.generatedKeys\n")
    search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean, text=True).strip()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(scratch), search]))
    subprocess.run(["lean", "--root", scratch, "-o", modules / "KeygenProgram.olean", source],
                   cwd=lean, env=env, check=True)
    proof = lean / "Cachepath/Keygen.lean"
    fail = subprocess.run(["lean", proof], cwd=lean, env=env, capture_output=True, text=True)
    theorem_start = next(i for i, line in enumerate(proof.read_text().splitlines(), 1) if line.startswith("theorem keygen_spec "))
    errors = re.findall(r"Keygen\.lean:(\d+):\d+: error", fail.stdout + fail.stderr)
    if not fail.returncode or not errors or min(map(int, errors)) < theorem_start:
        raise ValueError("expected a failure inside keygen_spec for the altered write: " + fail.stdout + fail.stderr)
    print("Lean rejected a regenerated keygen that copies the PRF seed into SK.PKseed.", flush=True)


def main():
    facade["run"](["lake", "build", "Cachepath.PlatformPortable"], lean)
    with tempfile.TemporaryDirectory() as directory:
        for target in (*facade["TARGETS"], "riscv64gc-unknown-none-elf"):
            scratch = Path(directory) / target
            scratch.mkdir()
            replay(target, scratch)
            check_typed(target, scratch)
            print(f"{target}: matched keygen_with_cache and proved all 12 typed keygen round trips and 12 constructors", flush=True)
        reject_wrong_seed(Path(directory))
    facade["audit_theorems"]("Cachepath.KeygenVerify", [
        "CacheopsRust.cache.generatedKeys.keygen_spec",
        "CacheopsRust.Public.keygen_then_sign_many",
        "CacheopsRust.Public.scalar_keygen_then_sign_many",
        "CacheopsRust.Public.scalar_keygen_sign_verify",
    ])


if __name__ == "__main__":
    main()
