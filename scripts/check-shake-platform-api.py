#!/usr/bin/env python3
"""Check named SHAKE APIs against independently extracted target-specific Rust."""
import re
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
common = facade["common"]
LEAN = facade["LEAN"]
SETS = tuple(s.replace("sha2_", "shake_") for s in common["SETS"])
OPS = common["OPERATIONS"]
PLATFORMS = {
    "Apple": ("aarch64-apple-darwin", "KappleouterRust", "Kadisp"),
    "Linux": ("aarch64-unknown-linux-gnu", "KspongeLRust", "Kldisp"),
    "X86": ("x86_64-unknown-linux-gnu", "KxouterRust", "Kxdispatch"),
}

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
    print(f"{target_namespace}: verified {len(SETS)*len(OPS)} fixed-size SHAKE operations"
         , flush=True)


def forest(package, platform, scratch):
    _, target, machine = PLATFORMS[platform]
    sponge = f"ShakeForest{platform}"
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


def linux_dispatch(scratch):
    module = "crate::shake256::parallel::"
    path = facade["extract"]("rust", "aarch64-unknown-linux-gnu", "LinuxDispatch", scratch,
                             (module + "available", module + "permute"), (module + "mixed::permute",))
    model = (LEAN / "Shakebatch/LinuxDispatch.lean").read_text()
    actual = list(common["declarations"](common["body"](path / "Funs.lean")))
    if len(actual) != 2 or any(definition not in model for definition in actual):
        raise ValueError("unexpected Linux SHAKE dispatch body")
    external = list(common["declarations"]((path / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]))
    if len(external) != 1:
        raise ValueError("unexpected Linux SHAKE dispatch dependencies")
    match = re.fullmatch(r"axiom shake256.parallel.mixed.permute\s*:\s*(.*)", external[0], re.DOTALL)
    if not match:
        raise ValueError("unexpected Linux SHAKE dispatch signature")
    code = ("import Shakebatch.LinuxDispatch\nopen Aeneas Aeneas.Std Result\n"
            f"example : {match[1]} := KmixedpermRust.shake256.parallel.mixed.permute\n"
            "#print axioms slhdsa.Kldisp.permutation_of_round")
    result = common["run"](["lake", "env", "lean", "--stdin"], LEAN, input=code,
                           text=True, stdout=subprocess.PIPE)
    if "depends on axioms: [propext, Classical.choice, Quot.sound]" not in " ".join(result.stdout.split()):
        raise ValueError("unexpected Linux SHAKE dispatch axioms")


def facade_adapter(target, scratch):
    operations = ("append", "sign_into", "sign_internal_into", "keygen_seeds",
                  "signing_key_from", "signature_from", "bytes_equal")
    roots = tuple(f"crate::shake::adapter::{name}" for name in operations)
    cuts = tuple(f"crate::shake::slh::{name}" for name in
                 ("with_context", "slh_sign_internal", "slh_keygen_internal"))
    package = facade["extract"]("rust", target, "ShakeAdapter", scratch, roots, cuts)
    for filename in ("Funs.lean", "Types.lean"):
        known = set(common["declarations"](common["body"](LEAN / "Slhdsa" / filename)))
        actual = set(common["declarations"](common["body"](package / filename)))
        if actual - known:
            raise ValueError(f"unmatched SHAKE facade implementation: {actual - known}")
    declared = common["declarations"]((package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1])
    names = {re.search(r"axiom ([^\s:]+)", d)[1] for d in declared}
    if names != {cut.replace("crate::", "").replace("::", ".") for cut in cuts}:
        raise ValueError(f"unexpected SHAKE adapter cut on {target}: {names}")


def audit_facade(platform, width_three=False):
    roots = [f"slh_dsa.{s}_{op}" for s in SETS for op in
             ("sign", "sign_with_context", "verify", "verify_with_context",
              "randomized_sign", "new", "parsers", "der")]
    roots += [f"slh_dsa.Kat.{s}_{op}" for s in SETS for op in ("algorithms", "errors")]
    roots += [f"slh_dsa.multipart_{s}_eq" for s in ("sign", "verify", "randomized")]
    # Functionally unchanged definitions may be shared with the portable facade.
    namespace = "WidthThreeSignedFacade" if width_three else f"NativeShake{platform}Facade"
    module = "Shakebatch.WidthThreeNative" if width_three else f"Shakebatch.{platform}Facade"
    source = [f"import {module}", "open Lean Elab Command"]
    for name in roots:
        prefix = namespace
        require_native = (not name.startswith("slh_dsa.multipart_") if width_three else
                          name.endswith(("_sign", "_verify", "_algorithms", "_new")))
        source += ["run_cmd do",
                   f"  let n := if (← getEnv).contains `{prefix}.{name} then `{prefix}.{name} else `{name}",
                   f"  if n == `{name} && {str(require_native).lower()} then throwError \"missing native facade binding\"",
                   "  elabCommand (← `(#print axioms $(mkIdent n):ident))"]
    result = common["run"](["lake", "env", "lean", "--stdin"], LEAN,
                           input="\n".join(source), text=True, stdout=subprocess.PIPE)
    audit = " ".join(result.stdout.split())
    for name in roots:
        if not any(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" in audit
                   for n in (name, f"{namespace}.{name}")):
            raise ValueError(f"missing native facade theorem {name}")
    print(f"{platform}: verified {len(roots)} SHAKE facade theorem groups"
         , flush=True)


def check_platform(platform, scratch):
    target, raw, permutation = PLATFORMS[platform]
    if platform == "Linux":
        linux_dispatch(scratch)
        facade_adapter(target, scratch)
        for checker in ("check-native-shake-signing.py", "check-shake-width-three-xmss.py",
                        "check-shake-fors-scatter.py", "check-shake-active-hashes.py",
                        "check-shake-fors-fused.py", "check-shake-width-three-public.py",
                        "check-shake-parallel-public.py"):
            common["run"]([sys.executable, Path(__file__).with_name(checker)], LEAN.parent)
        audit_facade(platform, width_three=True)
        return
    dispatch = facade["extract"]("rust", target, "Dispatch", scratch,
        ("crate::shake::fors::fors_sign", "crate::shake::fors::fors_pk_from_sig"),
        ("crate::shake::batch", "crate::shake::fors_batch", "crate::shake::hash",
         "crate::shake::xmss", "crate::shake256"))
    forest(dispatch, platform, scratch)
    facade_adapter(target, scratch)
    audit_facade(platform)
    public = extraction(target, scratch)
    proof(public, [f"Shakebatch.{platform}Api"], native_models(platform, raw, permutation),
          f"NativeShake{platform}", raw, scratch)


if __name__ == "__main__":
    common["run"](["lake", "build", *(f"Shakebatch.{p}Facade" for p in PLATFORMS)], LEAN)
    for platform in PLATFORMS:
        with tempfile.TemporaryDirectory() as folder:
            check_platform(platform, Path(folder))
