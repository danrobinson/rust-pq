"""Bind the eight portable SHAKE entry-point proofs to independently extracted Rust."""
from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean-hw"
TARGETS = ("i686-unknown-linux-gnu", "powerpc64-unknown-linux-gnu", "riscv64gc-unknown-none-elf")
API = ("keygen", "public_key", "sign", "sign_deterministic", "verify")
INTERNAL = ("slh_keygen_internal", "slh_sign_internal", "slh_verify_internal")
os.environ["PATH"] = os.pathsep.join([str(Path.home()/".cargo/bin"), str(Path.home()/".elan/bin"), os.environ["PATH"]])


def body(path):
    text = path.read_text().split("\nnamespace slhdsa\n", 1)[1].rstrip()
    if not text.endswith("\nend slhdsa"):
        raise ValueError(path)
    return text.removesuffix("\nend slhdsa")


def check(target, folder):
    folder.mkdir()
    roots = ["crate::shake::api::" + op for op in API] + ["crate::shake::slh::" + op for op in INTERNAL]
    subprocess.run([ROOT/".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
                    *(arg for root in roots for arg in ("--start-from",root)), "--dest-file", folder/"slhdsa.llbc",
                    "--","--locked","--features","platform-sha2","--target",target],cwd=ROOT/"rust",check=True)
    subprocess.run([ROOT/".tools/aeneas/bin/aeneas","-backend","lean","-abort-on-error","-no-progress-bar",
                    "-split-files","-dest",folder,folder/"slhdsa.llbc"],cwd=ROOT,check=True)
    if list(folder.glob("*External*")):
        raise ValueError("portable SHAKE extraction reached an external function or type")
    decls = lambda path: {s.strip() for s in re.split(r"/--.*?-/",body(path),flags=re.S) if s.strip()}
    if decls(folder/"Types.lean") - decls(LEAN/"Slhdsa/Types.lean"):
        raise ValueError("fresh nominal types differ from checked structures")
    lines = ["import Shakeabs.Api", "open Aeneas Aeneas.Std Result ControlFlow Error",
             "open slhdsa", "set_option maxRecDepth 65536", "set_option maxHeartbeats 0",
             "noncomputable section", "namespace FreshPortable",
             "abbrev shake256.Sponge := ShakeAbsRust.shake256.Sponge", body(folder/"Funs.lean"), "end FreshPortable"]
    claims = []
    for op in API + INTERNAL:
        prefix = "" if op == "public_key" else "PortableShake."
        thm = prefix + "slhdsa.Shake." + ("api_" if op in API else "") + op + "_spec"
        entry = "shake." + ("api." if op in API else "slh.") + op
        old = prefix + "slhdsa." + entry
        new = "FreshPortable." + entry
        lines.append(f"run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry `{thm} `{old} `{new} `{new}_spec")
        lines.append(f"#print axioms {new}_spec")
        claims.append(new+"_spec")
    proof = folder/"Portable.lean"
    proof.write_text("\n".join(lines)+"\n")
    result = subprocess.run(["lake","env","lean",proof],cwd=LEAN,stdout=subprocess.PIPE,text=True)
    if result.returncode: raise RuntimeError(result.stdout)
    for claim in claims:
        if f"'{claim}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in result.stdout.splitlines():
            raise ValueError(claim)
    print(f"{target}: {len(claims)} complete SHAKE entry-point proofs",flush=True)


if __name__ == "__main__":
    subprocess.run(["lake","build","Shakeabs.Api"],cwd=LEAN,check=True)
    with tempfile.TemporaryDirectory() as scratch:
        for target in TARGETS:
            check(target,Path(scratch)/target)
