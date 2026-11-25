#!/usr/bin/env python3
"""Bind both Arm hosts' native SLH-DSA proofs directly to fresh serial SDK callers."""
from pathlib import Path
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
arm = facade["common"]
ROOT, LEAN, run = (arm[k] for k in ("ROOT", "LEAN", "run"))
SETS = arm["SETS"]
OPS = arm["INTERNAL"] + arm["CONTEXT"]
NATIVE = ("fors.fors_sign", "fors.fors_pk_from_sig", "ht.ht_sign", "ht.ht_verify")
INTRINSICS = ("crate::sha256::hw::arm", "crate::sha512::hw::arm",
              "sha2::sha256::compress256", "sha2::sha512::compress512")
HOSTS = {"aarch64-apple-darwin": "", "aarch64-unknown-linux-gnu": "LinuxArmSdk."}


def extract(target, scratch):
    roots = [f"crate::sets::{s}::{op}" for s in SETS for op in OPS]
    cuts = ["crate::" + name.replace(".", "::") for name in NATIVE]
    return facade["extract"]("rust", target, "Fresh", scratch, roots, cuts + list(INTRINSICS))


def shared_types(package):
    decls, body = arm["declarations"], arm["body"]
    stable = set(decls(body(LEAN / "Slhdsa/Types.lean")))
    segmented = {d: "SegmentedRust" for d in decls(body(LEAN / "Segmented/Types.lean", "SegmentedRust"))}
    for d in decls(body(LEAN / "Segmentedapi/Types.lean", "SegmentedApiRust")):
        if re.match(r"@\[reducible\]\s*def slh\.message\.Sha(?:256|512) :=", d):
            segmented[d] = "SegmentedApiRust"
    aliases = []
    for d in decls(body(package / "Types.lean")):
        if d in stable:
            continue
        if d not in segmented:
            raise ValueError(f"unmatched source type {d}")
        name = re.search(r"(?:structure|def) (slh\.message\.\w+)", d).group(1)
        aliases.append(f"abbrev {name} := {segmented[d]}.{name}")
    return aliases


def verify(package, target, scratch):
    linux = HOSTS[target]
    native = linux + "slhdsa.NativeArmSignature."
    context = linux + "ArmSdk.AppleContext.slhdsa.SegmentedApi.Program."
    sdk = linux + "ArmSdk.AppleContext.SegmentedSdk.slhdsa."
    internal = linux + "ArmInternal.AppleInternal.slhdsa."
    body = arm["body"](package / "Funs.lean")
    names = set(re.findall(r"\bdef ([\w.]+)", body))
    required = ({f"sets.{s}.{op}" for s in SETS for op in OPS} |
                {"slh.slh_sign_internal", "slh.slh_verify_internal", "slh.message.sign",
                 "slh.message.verify", "slh.slh_sign", "slh.slh_verify"})
    if required - names:
        raise ValueError(f"missing extracted entry points on {target}: {required - names}")
    if len(required) != 48:
        raise ValueError("expected six generic and 42 fixed signing and verification callers")
    # Those four closed native dispatchers carry both feature records. All message
    # handling, SHA-256/SHA-512 streams, seed expansion and scalar hash wrappers
    # remain in the fresh translation down to the explicit hardware interfaces.
    bindings = {name: f"@{native}{name} cpu features N" for name in NATIVE}
    source = ["import Armwide.LinuxSignature", "open Aeneas Aeneas.Std Result ControlFlow Error",
              "open slhdsa", "set_option maxHeartbeats 0", "set_option maxRecDepth 65536",
              "set_option linter.concreteInstances false", "noncomputable section", "namespace FreshArm",
              "variable [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features]",
              *shared_types(package), arm["checked_external_bindings"](package, bindings), body, "end FreshArm"]
    for name in ("slh.message.sign", "slh.message.verify", "slh.slh_sign", "slh.slh_verify"):
        source.append(f"example : @FreshArm.{name} = @{context}{name} := by rfl'")
    for name, selected in (
        ("sha256.sha256_from", "ArmStreamRust.sha256.sha256_from"),
        ("sha512.sha512_from", "ArmStreamRust.sha512.sha512_from"),
        ("sha256.compress", "slhdsa.sha256.compress"),
        ("sha512.compress", ("ArmStreamRust." if linux else "slhdsa.") + "sha512.compress"),
    ):
        source.append(f"example : @FreshArm.{name} = @{selected} := by rfl'")
    def attach(theorem, reference, actual):
        source.append("run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry "
                      f"`{theorem} `{reference} `FreshArm.{actual} `FreshArm.{actual}_fips")
    for op in arm["INTERNAL"]:
        attach(native + op + "_spec", native + "slh." + op, "slh." + op)
    for s in SETS:
        for op in OPS:
            owner = internal if op in arm["INTERNAL"] else sdk
            name = f"sets.{s}.{op}"
            attach(owner + s + "." + op + "_spec", owner + name, name)
    proof = scratch / "Source.lean"
    proof.write_text("\n".join(source) + "\n")
    run(["lake", "env", "lean", proof], LEAN)
    print(f"{target}: bound all six generic and 42 fixed native signature entries", flush=True)


def main():
    run(["lake", "build", "Armwide.LinuxSignature"], LEAN)
    for host in HOSTS:
        with tempfile.TemporaryDirectory() as work:
            scratch = Path(work)
            verify(extract(host, scratch), host, scratch)


if __name__ == "__main__":
    main()
