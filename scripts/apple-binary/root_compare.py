"""Check the final AArch64 root comparison against independent root locations in Lean."""
import argparse
import os
from pathlib import Path
import subprocess

from image import Image, require

ROOT = Path(__file__).resolve().parents[2]


def certificate(image):
    lines = [
        "import Spec.ArmRootComparison",
        "open LinkedArm.RootComparison",
        "set_option linter.unusedSimpArgs false",
        "namespace LinkedRootWitness",
    ]
    for shake in (True, False):
        prefix = b"6slhdsa5shake" if shake else b"6slhdsa"
        for width in (16, 24, 32):
            suffix = f"Kj{width:x}_EB{6 if shake else 4}_".encode()
            regular = b"3slh19slh_verify_internal" if width == 16 else b"2ht9ht_verify"
            symbols = [(prefix + regular + suffix, False)]
            if not shake and width == 16:
                symbols.append((prefix + b"3slh7message6verifyKj10_EB6_", True))
            for symbol, segmented in symbols:
                pc, words = image.function(symbol, prefix)
                (end,) = [i for i, word in enumerate(words) if word == 0x1A9F17E0]
                if width == 16:
                    count = 6 if segmented else 5
                    lhs = "(s.regs 29 - 160)"
                    rhs = f"(s.sp + {40 if segmented else 64})"
                else:
                    count = 5 + width // 8 + 1
                    lhs = f"(s.sp + {32 if shake else 16})"
                    rhs = "(m (s.sp + 8))" if shake else "(m s.sp)"
                start = end + 1 - count
                require(start >= 0, "missing root comparison")
                ops = ", ".join(hex(w) for w in words[start : end + 1])
                name = f"{'shake' if shake else 'sha2'}_{width}_{'seg' if segmented else 'ordinary'}"
                byte_rhs = rhs.replace("(m ", "(load64 m ")
                lines.extend([
                    f"-- Linked entry {pc:#x}, comparison starts at {pc + 4*start:#x}.",
                    f"theorem {name} (m : Memory) (s : State) :",
                    f"    verdict [{ops}] m s =",
                    f"    some (if root m {lhs} {width//8} = root m {rhs} {width//8} then 1 else 0) := by",
                    "  simp [verdict, step, root, base, operand, write, List.range_succ, List.foldlM,",
                    "    Bool.and_assoc, Bool.and_eq_true, and_assoc, BitVec.sub_eq_add_neg, BitVec.add_assoc]",
                    f"theorem {name}_bytes (m : ByteMemory) (s : State) :",
                    f"    verdict [{ops}] (load64 m) s =",
                    f"    some (if byteSlice m {lhs} {width} = byteSlice m {byte_rhs} {width} then 1 else 0) := by",
                    f"  rw [{name}]",
                    "  simp [root, List.range_succ, load64_eq, byteSlice, and_assoc, BitVec.add_assoc]",
                ])
    lines.append("end LinkedRootWitness")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    body = certificate(Image(args.binary.read_bytes()))
    env = dict(os.environ, PATH=str(Path.home() / ".elan/bin") + os.pathsep + os.environ["PATH"])
    cmd = ["lake", "env", "lean", "--stdin"]
    subprocess.run(cmd, input=body, text=True, check=True, cwd=ROOT/"lean", env=env)
    if args.self_test:
        # Make the first comparison compare a register with itself.
        mutant = body.replace("0xeb0b013f", "0xeb09013f", 1)
        require(mutant != body, "control did not change a word")
        trial = subprocess.run(cmd, input=mutant, text=True, capture_output=True, cwd=ROOT/"lean", env=env)
        require(trial.returncode != 0 and "unsolved goals" in trial.stdout, "unexpected mutation result")
    print("Lean checked all seven linked root comparison blocks")


if __name__ == "__main__":
    main()
