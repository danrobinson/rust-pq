#!/usr/bin/env python3
"""Check named SHAKE APIs against independently extracted target-specific Rust."""
import re
import runpy
import tempfile
from pathlib import Path

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
common = facade["common"]
LEAN = facade["LEAN"]
SETS = tuple(s.replace("sha2_", "shake_") for s in common["SETS"])
OPS = common["OPERATIONS"]

# Every crate function not listed as a cut is emitted by Charon and Aeneas.
CUTS = ("crate::shake::batch", "crate::shake::fors_batch", "crate::shake256")
BASE = {"shake256.Sponge.new", "shake256.Sponge.absorb", "shake256.Sponge.finish",
        "shake.batch.available", "shake.batch.keygen", "shake.batch.sign", "shake.batch.recover",
        "shake.fors_batch.sign", "shake.fors_batch.recover"}


def native_models(platform, raw, permutation):
    stream = f"ShakeForest{platform}.slhdsa.ShakeBatch.scalarStream"
    machine = f"slhdsa.{permutation}.machine"
    batch = "slhdsa.ShakeBatch.shake"
    return {
        "shake256.Sponge.new": f"{raw}.shake256.Sponge.new",
        "shake256.Sponge.absorb": f"{raw}.shake256.Sponge.absorb",
        "shake256.Sponge.finish": f"{raw}.shake256.Sponge.finish",
        "shake.batch.available": f"slhdsa.ShakeBatch.{platform}.available",
        "shake.batch.keygen": f"{batch}.batch.keygen {machine} {stream}",
        "shake.batch.sign": f"{batch}.batch.sign {machine}",
        "shake.batch.recover": f"{batch}.batch.recover {machine} {stream}",
        "shake.fors_batch.sign": f"{batch}.fors_batch.sign {machine}",
        "shake.fors_batch.recover": f"{batch}.fors_batch.recover {machine} {stream}",
    }


def extraction(target, folder):
    roots = tuple(f"crate::sets::{s}::{op}" for s in SETS for op in OPS)
    return facade["extract"]("rust", target, "Public", folder, roots, CUTS)


def proof(package, imports, bindings, target_namespace, raw, scratch):
    types = set(common["declarations"](common["body"](LEAN / "Slhdsa/Types.lean")))
    fresh = set(common["declarations"](common["body"](package / "Types.lean")))
    if fresh - types:
        raise ValueError(f"unmatched data types: {fresh - types}")
    external_types = (package / "TypesExternal_Template.lean").read_text()
    if list(common["declarations"](external_types[external_types.index("/-- "):])) != ["axiom shake256.Sponge : Type"]:
        raise ValueError("unexpected public sponge state type")
    provided = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    aliases = []
    seen = set()
    for decl in common["declarations"](provided):
        match = re.fullmatch(r"axiom ([^\s]+)\s*(.*)", decl, re.DOTALL)
        if not match or match[1] not in BASE:
            raise ValueError(f"unexpected entry-point binding: {decl}")
        name, signature = match.groups()
        binders = signature.rpartition(":")[0]
        args = re.findall(r"[{(]([^ :{}()]+)\s*:", binders)
        aliases.append(f"abbrev {name} {signature} := @{bindings[name]} {' '.join(args)}")
        seen.add(name)
    if set(bindings) != seen or seen != BASE:
        raise ValueError("one or more of the nine algorithm bindings is missing")
    code = [*(f"import {name}" for name in imports), "open Aeneas Aeneas.Std Result ControlFlow Error",
            "set_option maxRecDepth 65536", "set_option maxHeartbeats 0", "noncomputable section",
            "open slhdsa", "namespace FreshSDK", f"abbrev shake256.Sponge := {raw}.shake256.Sponge", *aliases, common["body"](package / "Funs.lean"), "end FreshSDK"]
    for s in SETS:
        for op in OPS:
            old = f"slhdsa.sets.{s}.{op}"
            claim = f"slhdsa.{s}.{op}_spec"
            actual = f"FreshSDK.sets.{s}.{op}"
            # When a definition has no substituted dependency, replay keeps the original constant.
            code.extend(["open Lean Elab Command in", "run_cmd liftCoreM do",
                         f"  let old := if (← getEnv).contains `{target_namespace}.{old} then `{target_namespace}.{old} else `{old}",
                         f"  PlatformProof.bindEntry `{target_namespace}.{claim} old `{actual} `{actual}_fips",
                         f"#print axioms {actual}_fips"])
    input_path = scratch / "Fresh.lean"
    input_path.write_text("\n".join(code))
    import subprocess
    proc = subprocess.run(["lake", "env", "lean", input_path], cwd=LEAN, stdout=subprocess.PIPE, text=True)
    if proc.returncode:
        raise RuntimeError(proc.stdout)
    audit = set(proc.stdout.splitlines())
    for s in SETS:
        for op in OPS:
            name = f"FreshSDK.sets.{s}.{op}_fips"
            if f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in audit:
                raise ValueError(f"unverified public claim {name}")
    print(f"{target_namespace}: verified {len(SETS)*len(OPS)} fixed-size SHAKE operations", flush=True)


def forest(package, platform, scratch):
    target, sponge, machine = {
        "Apple": ("KappleouterRust","ShakeForestApple","Kadisp"),
        }[platform]
    owner = f"slhdsa.ShakeBatch.{platform}"
    stream = f"{sponge}.slhdsa.ShakeBatch.scalarStream"
    types = set(common["declarations"](common["body"](LEAN/"Slhdsa/Types.lean")))
    fresh_types = set(common["declarations"](common["body"](package/"Types.lean")))
    if fresh_types - types:
        raise ValueError(f"unexpected {platform} forest types")
    fresh = (package/"TypesExternal_Template.lean").read_text()
    if list(common["declarations"](fresh[fresh.index("/-- "):])) != ["axiom shake256.Sponge : Type"]:
        raise ValueError(f"unexpected {platform} forest state")
    models = {
        "shake.xmss.climb": f"@{sponge}.slhdsa.shake.xmss.climb",
        "shake.batch.available": f"@{owner}.available",
        "shake.hash.thash": f"@{sponge}.slhdsa.shake.hash.thash",
        "shake.hash.thash_pair": f"@{sponge}.slhdsa.shake.hash.thash_pair",
        "shake.fors_batch.sign": f"@slhdsa.ShakeBatch.shake.fors_batch.sign slhdsa.{machine}.machine",
        "shake.fors_batch.recover": f"@slhdsa.ShakeBatch.shake.fors_batch.recover slhdsa.{machine}.machine {stream}",
        "shake256.Sponge.absorb": f"@{target}.shake256.Sponge.absorb",
        "shake.hash.digest": f"@{sponge}.slhdsa.shake.hash.digest",
        "shake.hash.start": f"@{sponge}.slhdsa.shake.hash.start",
    }
    lines = [f"import Shakebatch.{platform}Fors","open Aeneas Aeneas.Std Result ControlFlow Error slhdsa",
             "set_option maxRecDepth 65536","set_option maxHeartbeats 0","noncomputable section",
             "namespace FreshForest",f"abbrev shake256.Sponge := {target}.shake256.Sponge"]
    seen = set()
    for decl in common["declarations"]((package/"FunsExternal_Template.lean").read_text().split("open slhdsa",1)[1]):
        match = re.fullmatch(r"axiom ([^\s]+)\s*(.*)",decl,re.DOTALL)
        if not match or match[1] not in models:
            raise ValueError(f"unexpected forest binding {decl}")
        name,signature = match.groups()
        args = re.findall(r"[{(]([^ :{}()]+)\s*:", signature.rpartition(":")[0])
        lines.append(f"abbrev {name} {signature} := {models[name]} {' '.join(args)}")
        seen.add(name)
    if seen != set(models):
        raise ValueError("missing a forest binding")
    lines.extend([common["body"](package/"Funs.lean"),"end FreshForest"])
    for name,alias in (("fors_sign","sign"),("fors_pk_from_sig","recover")):
        actual = f"FreshForest.shake.fors.{name}"
        lines.append(f"run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry `{owner}.{name}_spec `{owner}.{alias} `{actual} `{actual}_fips")
        lines.append(f"#print axioms {actual}_fips")
    input_path=scratch/"FreshForest.lean"
    input_path.write_text("\n".join(lines)+"\n")
    import subprocess
    proc=subprocess.run(["lake","env","lean",input_path],cwd=LEAN,stdout=subprocess.PIPE,text=True)
    if proc.returncode:
        raise RuntimeError(proc.stdout)
    for name in ("fors_sign","fors_pk_from_sig"):
        if f"'FreshForest.shake.fors.{name}_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" not in proc.stdout.splitlines():
            raise ValueError(f"missing native forest proof {name}")
    print(f"{platform}: fresh FORS signer and verifier use verified native operations",flush=True)


if __name__ == "__main__":
    common["run"](["lake","build","Shakebatch.AppleApi"],LEAN)
    with tempfile.TemporaryDirectory() as folder:
        p=Path(folder)
        dispatch=facade["extract"]("rust","aarch64-apple-darwin","Dispatch",p,
            ("crate::shake::fors::fors_sign","crate::shake::fors::fors_pk_from_sig"),
            ("crate::shake::batch","crate::shake::fors_batch","crate::shake::hash","crate::shake::xmss","crate::shake256"))
        forest(dispatch,"Apple",p)
        public = extraction("aarch64-apple-darwin",p)
        proof(public,["Shakebatch.AppleApi"],native_models("Apple", "KappleouterRust", "Kadisp"),
              "NativeShakeApple", "KappleouterRust", p)
