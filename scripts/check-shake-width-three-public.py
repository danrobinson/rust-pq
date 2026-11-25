#!/usr/bin/env python3
"""Attach all six Linux Arm SHAKE public APIs to the width-three composition."""
from pathlib import Path
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
sdk = runpy.run_path(str(HERE / "check-shake-platform-api.py"))
facade, arm = sdk["facade"], sdk["common"]
MODEL = "WidthThreeLinuxSDK.slhdsa.WidthThree."
CUTS = {
    "shake256.Sponge.new": "@KspongeLRust.shake256.Sponge.new",
    "shake256.Sponge.absorb": "@KspongeLRust.shake256.Sponge.absorb",
    "shake256.Sponge.finish": "@KspongeLRust.shake256.Sponge.finish",
    "shake.xmss.xmss_node": "@slhdsa.WidthThree.linuxNode",
    "shake.xmss.xmss_sign": "@" + MODEL + "signXmss w.c.wots",
    "shake.xmss.xmss_pk_from_sig": "@slhdsa.WidthThree.verifiedXmss",
    "shake.fors.fors_sign": "@slhdsa.WidthThree.forsSign w.c",
    "shake.fors.fors_pk_from_sig": "@slhdsa.WidthThree.verifiedFors",
}


def check(package, scratch):
    lean = arm["LEAN"]
    shared = set(arm["declarations"](arm["body"](lean / "Slhdsa/Types.lean")))
    if set(arm["declarations"](arm["body"](package / "Types.lean"))) - shared:
        raise ValueError("fresh SHAKE SDK has unmodeled nominal types")
    externals = (package / "TypesExternal_Template.lean").read_text()
    if list(arm["declarations"](externals[externals.index("/-- "):])) != ["axiom shake256.Sponge : Type"]:
        raise ValueError("unexpected Linux SHAKE SDK type boundary")
    lines = ["import Shakebatch.WidthThreeRoundTrip", "open Aeneas Aeneas.Std Result ControlFlow Error slhdsa",
             "set_option maxHeartbeats 0", "set_option maxRecDepth 65536",
             "set_option linter.concreteInstances false", "noncomputable section", "namespace FreshWidth",
             "class Witness where c : slhdsa.WidthThree.SigningPrimitives", "variable [w : Witness]",
             "abbrev shake256.Sponge := KspongeLRust.shake256.Sponge"]
    external = (package / "FunsExternal_Template.lean").read_text()
    seen = set()
    for d in arm["declarations"](external[external.index("/-- "):]):
        match = re.fullmatch(r"axiom (\S+)\s*(.*)", d, re.S)
        if not match or match[1] not in CUTS:
            raise ValueError(f"unexpected SDK boundary: {d}")
        name, signature = match.groups()
        seen.add(name)
        args = re.findall(r"[{(]([^ :{}()]+)\s*:", signature.rpartition(":")[0])
        lines.append(f"abbrev {name} {signature} := {CUTS[name]} {' '.join(args)}")
    if seen != set(CUTS):
        raise ValueError(f"missing SDK primitives: {set(CUTS)-seen}")
    # Share declarations which are byte-for-byte identical after dropping Rust
    # location comments and cannot reach a substituted primitive. In particular,
    # the FIPS parameters in the Aeneas output are deliberately irreducible.
    models = {}
    for path, owner in (("Slhdsa/Funs.lean", "slhdsa"), ("Shakeopt/Seg/Funs.lean", "ShakeoptSeg")):
        for d in arm["declarations"](arm["body"](lean / path, owner)):
            models.setdefault(d, owner)
    changed = set(CUTS)
    for d in arm["declarations"](arm["body"](package / "Funs.lean")):
        if d not in models:
            raise ValueError(f"public declaration changed: {d[:200]}")
        head = re.search(r"\bdef\s+(\S+)", d)
        if not head:
            raise ValueError(f"unexpected public declaration: {d[:120]}")
        name = head[1]
        refs = set(re.findall(r"[A-Za-z_][\w.]*", d[head.end():]))
        if refs & changed or (name.startswith("sets.") and not name.endswith(".PARAMS")):
            changed.add(name)
            lines.append(d)
        else:
            lines.append(f"abbrev {name} := @{models[d]}.{name}")
    lines += ["end FreshWidth", "open Lean Elab Command"]
    for suite in sdk["SETS"]:
        for op in sdk["OPS"]:
            raw = f"slhdsa.sets.{suite}.{op}"
            fresh = f"FreshWidth.sets.{suite}.{op}"
            theorem = f"slhdsa.{suite}.{op}_spec"
            if op == "public_key":
                lines += [f"example : @{fresh} = @{raw} := by rfl'", f"#print axioms {theorem}"]
            else:
                section = "SegmentedPublic." if op in ("sign", "sign_deterministic", "slh_sign", "verify", "slh_verify") else ""
                if op in ("keygen", "slh_keygen_internal"):
                    host = "WidthThreeKeygenSDK."
                    lines += [f"example : @{fresh} = @{host}{raw} := by rfl'"]
                elif op in ("verify", "slh_verify", "slh_verify_internal"):
                    host = "WidthThreeVerifySDK." + section
                    lines += [f"example : @{fresh} = @{host}{raw} := by rfl'"]
                else:
                    host = "WidthThreeLinuxSDK.WidthThreeSDK." + section
                    lines += [f"example [w : FreshWidth.Witness] : @{fresh} w = @{host}{raw} w.c := by rfl'"]
                claim = (f"slhdsa.WidthThree.AllLengths.{suite}.{op}"
                         if op in ("sign", "slh_sign", "verify", "slh_verify", "sign_deterministic")
                         else host + theorem)
                lines.append(f"#print axioms {claim}")
    output = scratch / "Fresh.lean"
    output.write_text("\n".join(lines))
    import subprocess
    run = subprocess.run(["lake", "env", "lean", output], cwd=lean, capture_output=True, text=True)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
    audit = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", run.stdout)
    if len(audit) != len(sdk["SETS"]) * len(sdk["OPS"]):
        raise ValueError(f"incomplete public axiom audit: {run.stdout}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, axioms in audit:
        if set(re.findall(r"[A-Za-z_.]+", axioms)) - allowed:
            raise ValueError(f"unexpected axiom in {name}: {axioms}")
    print("Linux Arm: the 60 fresh public entry points match their audited width-three FIPS proofs")


def main():
    arm["run"](["lake", "build", "Shakebatch.WidthThreeRoundTrip"], arm["LEAN"])
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        roots = [f"crate::sets::{s}::{op}" for s in sdk["SETS"] for op in sdk["OPS"]]
        cuts = ["crate::" + name.replace(".", "::") for name in CUTS if not name.startswith("shake256.")]
        package = facade["extract"]("rust", "aarch64-unknown-linux-gnu", "WidthThreeSDK", scratch,
                                    roots, cuts + ["crate::shake256"])
        check(package, scratch)
    facade["audit_theorems"]("Shakebatch.WidthThreeRoundTrip", [
        "slhdsa.WidthThree.serial_roundtrip", "slhdsa.WidthThree.serial_keygen_parallel_sign_roundtrip"])


if __name__ == "__main__":
    main()
