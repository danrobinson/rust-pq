#!/usr/bin/env python3
"""Check fixed-size Linux SHAKE signing wrappers compiled with Cargo's parallel feature."""
from pathlib import Path
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
cache = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
arm = cache["facade"]["common"]
sdk = runpy.run_path(str(HERE / "check-shake-platform-api.py"))
OPS = ("slh_sign_internal", "slh_sign", "sign", "sign_deterministic")
CUTS = {"shake.slh.slh_sign_internal": "parallelInternal", "shake.slh.shake_sign_ctx": "parallelContext"}


def main():
    lean = arm["LEAN"]
    arm["run"](["lake", "build", "Shakebatch.WidthThreeParallel"], lean)
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        pkg = cache["extract_target"]("aarch64-unknown-linux-gnu", scratch,
            [f"crate::sets::{s}::{op}" for s in sdk["SETS"] for op in OPS],
            ["crate::" + name.replace(".", "::") for name in CUTS], features="parallel")
        shared_types = set(arm["declarations"](arm["body"](lean / "Slhdsa/Types.lean")))
        fresh_types = set(arm["declarations"](arm["body"](pkg / "Types.lean", "CacheopsRust")))
        if fresh_types - shared_types:
            raise ValueError("unrecognized nominal types in the SHAKE source extraction")
        models = set()
        for path, owner in (("Slhdsa/Funs.lean", "slhdsa"), ("Shakeopt/Seg/Funs.lean", "ShakeoptSeg")):
            models.update(arm["declarations"](arm["body"](lean / path, owner)))
        lines = ["import Shakebatch.WidthThreeParallel", "open Aeneas Aeneas.Std Result ControlFlow slhdsa",
                 "set_option maxHeartbeats 0", "set_option maxRecDepth 65536", "noncomputable section",
                 "set_option linter.concreteInstances false", "namespace FreshParallelSDK",
                 "class Provider where c : WidthThree.ParallelPrimitives", "variable [w : Provider]"]
        external = (pkg / "FunsExternal_Template.lean").read_text()
        seen = set()
        for d in arm["declarations"](external[external.index("/-- "):]):
            match = re.fullmatch(r"axiom (\S+)\s*(.*)", d, re.S)
            if not match or match[1] not in CUTS:
                raise ValueError(f"unexpected signing primitive: {d}")
            name, signature = match.groups()
            seen.add(name)
            lines.append(f"abbrev {name} {signature} := @WidthThree.{CUTS[name]} w.c N")
        if seen != set(CUTS):
            raise ValueError("missing parallel internal or segmented signer")
        for d in arm["declarations"](arm["body"](pkg / "Funs.lean", "CacheopsRust")):
            if d not in models:
                raise ValueError(f"changed parallel SDK caller: {d[:200]}")
            lines.append(d)
        lines.append("end FreshParallelSDK")
        for suite in sdk["SETS"]:
            for op in OPS:
                host = "WidthThreeParallel." + ("" if op == "slh_sign_internal" else "SegmentedPublic.")
                raw = f"sets.{suite}.{op}"
                lines.append(f"example [w : FreshParallelSDK.Provider] : @FreshParallelSDK.{raw} w = @{host}slhdsa.{raw} w.c := by rfl'")
                lines.append(f"#print axioms {host}slhdsa.{suite}.{op}_spec")
        path = scratch / "Fresh.lean"
        path.write_text("\n".join(lines))
        import subprocess
        run = subprocess.run(["lake", "env", "lean", path], cwd=lean, capture_output=True, text=True)
        if run.returncode:
            raise ValueError(run.stdout + run.stderr)
        audit = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", run.stdout)
        if len(audit) != len(OPS)*len(sdk["SETS"]) or any(
            set(re.findall(r"[A-Za-z_.]+", a)) - {"propext", "Classical.choice", "Quot.sound"} for _, a in audit):
            raise ValueError("incomplete parallel SHAKE SDK axiom audit")
        print("Linux Arm: all 24 parallel SHAKE signing APIs match the conditional worker-or-fallback proofs")


if __name__ == "__main__":
    main()
