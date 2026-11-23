#!/usr/bin/env python3
"""Compose the target-specific compiled facade dictionaries with the independent peer."""
from pathlib import Path
import runpy
import subprocess
import tempfile

api = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
PLATFORMS = {
    "Apple": "AppleFacade",
    "Linux": "LinuxFacade.AppleFacade",
    "X86": "X86Facade",
}


def source(platform, sha_model):
    lines = ["import PeerEquality.Wire", f"import Platformadapter.{platform}",
             f"import Shakebatch.{platform}Facade", "open Spec slhdsa slhdsa.PeerCall",
             "open Lean Elab Term Meta", "set_option maxRecDepth 65536",
             "set_option maxHeartbeats 0"]
    # The keygen theorem names the concrete, source-bound Core dictionary.
    # Extract it from the proposition, preserving the exact constant and its type.
    lines += ['elab "core_of% " t:ident : term => do',
              '  let prop := (← getConstInfo (← resolveGlobalConstNoOverload t)).type',
              '  unless prop.isAppOf ``slh_dsa.KeygenCorrect do throwError "expected a keygen theorem, got {prop}"',
              '  return prop.getAppArgs[prop.getAppNumArgs-2]!']
    names = []
    for s in api["SETS"]:
        for family in ("sha2", "shake"):
            shape = s.split("_")[1]
            suite = family + "_" + shape
            owner = (sha_model + ".FacadeContext.FacadeAdapter" if family == "sha2" else
                     "NativeShake" + platform + "Facade") + ".slh_dsa." + suite
            slack = 409 if shape.startswith("128") else 561
            comparison = f"Compared{platform}.{suite}"
            names.extend([comparison, comparison + "_wire"])
            core = f"(core_of% {owner}_new)"
            params = "Spec." + suite
            selector = "." + shape[-1] + shape[:-1]
            peer = (f"(Providers.sha2 {selector} RcSlhSha2.nativeAlgorithms)" if family == "sha2"
                    else f"(Providers.shake {params})")
            route = " (route : RcSlhSha2.Routing)" if family == "sha2" else ""
            lines += [f"theorem {comparison}{route} : SameFacade {core} {params} {slack} {peer} := by"]
            if family == "sha2":
                lines.append(f"  apply (fun f => (sha2_link {selector} route f).2)")
            else:
                lines.append(f"  apply shake_link (by constructor <;> decide : {params}.Valid) (by rfl)")
            lines += [f"  apply facades_of_specs _ _ _ (by decide) {owner}_new",
                      f"  · intro k m ctx rnd hr hm; cases rnd <;> exact {owner}_sign_with_context _ _ _ _ hr hm",
                      f"  · exact {owner}_verify_with_context",
                      f"theorem {comparison}_wire{route} : WireFacade {core} {params} {slack} {peer} := by",
                      f"  apply wireFacade _ _ _ ({comparison}{' route' if route else ''})",
                      f"  · exact {owner}_parsers",
                      *(["  · decide"] * 4),
                      f"#print axioms {comparison}", f"#print axioms {comparison}_wire"]
    return "\n".join(lines), names


def main():
    modules = ["PeerEquality.Wire", *(f"Platformadapter.{p}" for p in PLATFORMS),
               *(f"Shakebatch.{p}Facade" for p in PLATFORMS)]
    api["run"](["lake", "build", *modules], api["LEAN"])
    with tempfile.TemporaryDirectory() as scratch:
        for platform, sha_model in PLATFORMS.items():
            program, names = source(platform, sha_model)
            path = Path(scratch) / f"{platform}.lean"
            path.write_text(program)
            run = subprocess.run(["lake", "env", "lean", path], cwd=api["LEAN"],
                                 stdout=subprocess.PIPE, text=True)
            if run.returncode:
                raise SystemExit(run.stdout)
            for name in names:
                if f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in " ".join(run.stdout.split()):
                    raise SystemExit(f"missing or unexpected axiom audit for {name}")
            print(f"{platform}: checked {len(names)} typed and wire peer equalities", flush=True)


if __name__ == "__main__":
    main()
