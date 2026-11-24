"""Verify the eight raw-key and DER operations on all twelve platform parameter sets."""
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGETS = ("x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu", "aarch64-apple-darwin")
SETS = [f"{family}_{bits}{speed}" for family in ("sha2", "shake") for bits in (128, 192, 256) for speed in "sf"]
OPS = ("public_key_from", "secret_key_from", "secret_keys_equal", "signature_len_ok",
       "pkcs8_encode", "pkcs8_decode", "spki_encode", "spki_decode")
os.environ["PATH"] = os.pathsep.join([str(Path.home()/".cargo/bin"), str(Path.home()/".elan/bin"), os.environ["PATH"]])


def body(path):
    text = path.read_text().split("\nnamespace slhdsa\n", 1)[1].rstrip()
    if not text.endswith("\nend slhdsa"):
        raise ValueError(path)
    return text.removesuffix("\nend slhdsa")


def declarations(path):
    return {d.strip() for d in re.split(r"/--.*?-/", body(path), flags=re.S) if d.strip()}


def extract(target, scratch):
    output = scratch/target
    output.mkdir()
    roots = [f"crate::sets::{s}::{op}" for s in SETS for op in OPS]
    subprocess.run([ROOT/".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
                    *(arg for root in roots for arg in ("--start-from", root)),
                    "--dest-file", output/"slhdsa.llbc", "--", "--locked", "--features",
                    "platform-sha2", "--target", target], cwd=ROOT/"rust", check=True)
    subprocess.run([ROOT/".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar",
                    "-split-files", "-dest", output, output/"slhdsa.llbc"], cwd=ROOT, check=True)
    if list(output.glob("*External*")):
        raise ValueError(f"{target}: unexpected external call or type")
    return output


def verify(package, scratch):
    if declarations(package/"Types.lean") - declarations(ROOT/"lean-hw/Slhdsa/Types.lean"):
        raise ValueError("unmatched nominal type in key encoding")
    lines = ["import Armplatform.Replay", "import Slhdsa.Proofs.Sets", "open Aeneas Aeneas.Std Result ControlFlow Error",
             "open slhdsa", "set_option maxRecDepth 65536", "set_option maxHeartbeats 0", "namespace EncodingTarget",
             body(package/"Funs.lean"), "end EncodingTarget"]
    expected = []
    for name in SETS:
        reference = "sha2_" + name.split("_",1)[1]
        dest = "Codec_" + name
        replacements = []
        for op in (*OPS, "SPKI_PREFIX", "PKCS8_PREFIX"):
            replacements.append(f"(`slhdsa.sets.{reference}.{op}, `EncodingTarget.sets.{name}.{op})")
        roots = [f"slhdsa.{reference}.{op}_" + ("eq" if op == "signature_len_ok" else "spec") for op in OPS]
        lines.append(f"run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.replay `{dest} [" +
                     ", ".join(replacements) + "] #[" + ", ".join("`" + r for r in roots) + "]")
        for op, root in zip(OPS, roots):
            theorem = dest + "." + root
            lines.extend([f"run_cmd do unless (← Lean.getConstInfo `{theorem}).type.getUsedConstants.contains "
                          f"`EncodingTarget.sets.{name}.{op} do throwError \"detached entry theorem\"",
                          f"#print axioms {theorem}"])
            expected.append(theorem)
    proof = scratch/"Encoding.lean"
    proof.write_text("\n".join(lines)+"\n")
    out = subprocess.run(["lake","env","lean",proof], cwd=ROOT/"lean-hw", stdout=subprocess.PIPE, text=True)
    if out.returncode:
        raise RuntimeError(out.stdout)
    for theorem in expected:
        reports = [s for s in out.stdout.splitlines() if s.startswith(f"'{theorem}' ")]
        if len(reports) != 1 or not re.fullmatch(r"'[^']+' (does not depend on any axioms|depends on axioms: \[(?:propext|Classical.choice|Quot.sound)(?:, (?:propext|Classical.choice|Quot.sound))*\])", reports[0]):
            raise ValueError(reports)
    print(f"Verified {len(expected)} named encoding paths on each of {len(TARGETS)} targets.")


if __name__ == "__main__":
    subprocess.run(["lake","build","Armplatform.Replay","Slhdsa.Proofs.Sets"], cwd=ROOT/"lean-hw", check=True)
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        packages = [extract(target,scratch) for target in TARGETS]
        for package in packages[1:]:
            for file in ("Types.lean","Funs.lean"):
                if (package/file).read_bytes() != (packages[0]/file).read_bytes():
                    raise ValueError(f"{package.name}: target-dependent code in {file}")
        verify(packages[0],scratch)
