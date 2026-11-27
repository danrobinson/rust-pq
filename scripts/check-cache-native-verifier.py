#!/usr/bin/env python3
"""Check each extracted verifier front end and audit its complete hosted recovery and cache theorems."""
from pathlib import Path
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
shared = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
LEAN = shared["LEAN"]
common = shared["facade"]["common"]


def check(target, name, sponge, functions, folder):
    fresh = shared["extract_target"](target, folder, ("crate::shake::api::verify",),
                                     ("crate::shake::wots::wots_pk_from_sig", "crate::shake::fors::fors_pk_from_sig",
                                      "crate::shake256"))
    parse = shared["generated_declarations"]
    types = parse(fresh / "Types.lean", "CacheopsRust", strict=True)
    original = parse(LEAN.parent / "lean/Slhdsa/Types.lean", "slhdsa")
    if any(original.get(k) != v for k,v in types.items()):
        raise ValueError(f"{target}: verifier data type changed")
    text = (fresh / "FunsExternal_Template.lean").read_text()
    import re
    expected = {"shake256.Sponge.new", "shake256.Sponge.finish", "shake256.Sponge.absorb",
                "shake.fors.fors_pk_from_sig", "shake.wots.wots_pk_from_sig"}
    if set(re.findall(r"\baxiom ([\w.]+)", text)) != expected:
        raise ValueError(f"{target}: unexpected verifier recovery boundary")
    if set(re.findall(r"\baxiom ([\w.]+)", (fresh / "TypesExternal_Template.lean").read_text())) != {"shake256.Sponge"}:
        raise ValueError(f"{target}: unexpected opaque state")
    code = f"""import Cachepath.NativeVerifierHosts
open Aeneas Aeneas.Std Result ControlFlow Error slhdsa
set_option maxRecDepth 65536
set_option maxHeartbeats 0
noncomputable section
namespace FreshVerifier
class Selection where
  recovery : CacheopsRust.NativeVerifier.Recovery
variable [picks : Selection]
abbrev shake256.Sponge := {sponge}.shake256.Sponge
abbrev shake256.Sponge.new := {sponge}.shake256.Sponge.new
abbrev shake256.Sponge.absorb := {functions}.shake256.Sponge.absorb
abbrev shake256.Sponge.finish := {functions}.shake256.Sponge.finish
abbrev shake.fors.fors_pk_from_sig := @CacheopsRust.NativeVerifier.Recovery.fors picks.recovery
abbrev shake.wots.wots_pk_from_sig := @CacheopsRust.NativeVerifier.Recovery.wots picks.recovery
{common["body"](fresh / "Funs.lean", "CacheopsRust")}
example (n : Usize) (p : slhdsa.params.Params) (m sig ctx pk : Slice U8) :
  shake.api.verify n p m sig ctx pk =
  {name}Verifier.VerifierWithRecovery.SegmentedPublic.slhdsa.shake.api.verify picks.recovery n p m sig ctx pk := by
  with_unfolding_all rfl
end FreshVerifier
"""
    path = folder / "Verify.lean"
    path.write_text(code)
    shared["facade"]["run"](["lake","env","lean",path],LEAN)
    print(f"{target}: kernel matched the entire live verifier up to the two recovery calls", flush=True)


def main():
    shared["facade"]["run"](["lake","build","Cachepath.NativeVerify.Hosted"],LEAN)
    for target,host,sponge,functions,short in (
        ("aarch64-apple-darwin","Apple","KappleouterRust","AppleSingleStream.KappleouterRust","appleFull"),
        ("aarch64-unknown-linux-gnu","Linux","KspongeLRust","KspongeLRust","linuxArmFull"),
        ("x86_64-unknown-linux-gnu","X86","KxouterRust","KxouterRust","linuxX86Full")):
        with tempfile.TemporaryDirectory(prefix="native-verify-") as work:
            check(target,host,sponge,functions,Path(work))
        shared["facade"]["audit_theorems"]("Cachepath.NativeVerifierHosts",[
            f"{host}Verifier.VerifierWithRecovery.SegmentedPublic.slhdsa.Shake.api_verify_spec",
            f"{host}CachedVerification.Hosted{host}Session.CacheopsRust.NativeSession.{short}",
        ])
    shared["facade"]["audit_theorems"]("Cachepath.NativeVerify.Hosted", [
        "CacheopsRust.NativeVerifier." + stem + result
        for stem in ("apple", "linuxArm", "linuxX86") for result in ("RoundTrip", "Verify")
    ])


if __name__ == "__main__":
    main()
