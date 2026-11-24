#!/usr/bin/env python3
"""Lift the production hybrid Keccak rounds to bitvectors and check them against FIPS 202."""
from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "rust/src/shake256/parallel.rs"
HERE = ROOT / "scripts/apple-keccak"


def lift_rounds(source):
    macro = source[source.index("macro_rules! round_function"):source.index('\n#[cfg(target_arch = "x86_64")]\nmacro_rules! permutation')]
    sha3 = source.split("mod sha3 {", 1)[1]
    operators = sha3[sha3.index("    macro_rules! xor3"):sha3.index('    round_function!')]
    rounds = sha3[sha3.index('    unsafe fn round_inplace'):sha3.index('    unsafe fn load_pair')]
    rounds = rounds[:rounds.rfind('    #[inline]')]
    neon = source.split("mod neon {", 1)[1]
    neon_ops = neon[neon.index("    macro_rules! xor3"):neon.index('    round_function!')]
    neon_round = 'mod neon { use super::*;\n' + neon_ops + macro.replace("unsafe fn round(", "pub(super) unsafe fn round(") + 'round_function!("neon"); }'
    code = neon_round + macro + operators + '\nround_function!("neon,sha3");\n' + rounds
    code = re.sub(r'#\[target_feature\(enable = (?:\$feature|"neon,sha3")\)\]', '', code)
    return re.sub(r'\bu64\b', 'Word', code)


def projected_round(i):
    # Lean checks this reduction of Spec.Keccak.round by definitional equality.
    def parity(x):
        return "(" + " ^^^ ".join(f"a[{x + 5*y}]!" for y in range(5)) + ")"
    def rho_pi(j):
        x, y = j % 5, j // 5
        k = (x + 3*y) % 5 + 5*x
        d = f"({parity((k+4)%5)} ^^^ (BitVec.rotateLeft {parity((k+1)%5)} 1))"
        r = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]
        return f"(BitVec.rotateLeft (a[{k}]! ^^^ {d}) {r[k]})"
    row = 5*(i//5)
    word = f"({rho_pi(i)} ^^^ ((~~~{rho_pi(row+(i+1)%5)}) &&& {rho_pi(row+(i+2)%5)}))"
    return f"({word} ^^^ c)" if i == 0 else word


def check_schedule(tmp, source):
    # Replace the two-lane memory intrinsics with checked indexing of the same
    # Rust row. Keep all dispatch arms, loops, round indices and store offsets.
    if not re.search(r'#\[cfg\(all\(target_arch = "aarch64", target_vendor = "apple"\)\)\]\s*pub\(crate\) const WIDTH: usize = 8;', source) or "type States = [[u64; WIDTH]; 25];" not in source:
        raise ValueError("review the Apple production state layout")
    sha3 = source.split("mod sha3 {", 1)[1]
    sha3 = sha3[sha3.index("    unsafe fn load_pair"):sha3.index("    pub(super) unsafe fn single")]
    neon = source.split("mod neon {", 1)[1].split("    pub(super) unsafe fn permute_active", 1)[1]
    neon = "    pub(super) unsafe fn permute_active" + neon.split("    pub(super) unsafe fn permute(", 1)[0]
    def module(name, body):
        body = re.sub(r'#\[target_feature\(enable = "[^"]+"\)\]', '', body)
        body = body.replace("unsafe { vld1q_u64(words[i].as_ptr().add(off)) }",
                            "[words[i][off], words[i][off+1]]")
        body = body.replace("unsafe { vst1q_u64(words[i].as_mut_ptr().add(off), a[i]) }",
                            "words[i][off..off+2].copy_from_slice(&a[i])")
        return "mod " + name + " { use super::*;\n" + body + "}\n"
    rc = re.search(r"const RC: \[u64; 24\] = \[(.*?)\];",
                   (ROOT/"rust/src/shake256.rs").read_text(), re.S)
    probe = (HERE/"schedule.rs").read_text().replace("// ROUND_CONSTANTS", rc[0])
    probe = probe.replace("// PRODUCTION", module("sha3", sha3) + module("neon", neon))
    (tmp/"schedule.rs").write_text(probe)
    subprocess.run(["rustc", tmp/"schedule.rs", "-o", tmp/"schedule"], check=True)
    subprocess.run([tmp/"schedule"], check=True)
    constants = ",".join(x.strip() for x in rc[1].split(",") if x.strip())
    return f"example : rc = #[{constants}] := by decide"


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"), str(Path.home()/".cargo/bin"), os.environ["PATH"]])
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        source = SRC.read_text()
        probe = (HERE / "rounds.rs").read_text().replace("// PRODUCTION", lift_rounds(source))
        (tmp / "rounds.rs").write_text(probe)
        subprocess.run(["rustc", tmp/"rounds.rs", "-o", tmp/"rounds"], check=True)
        expressions = subprocess.check_output([tmp/"rounds"], text=True).splitlines()
        if len(expressions) != 100:
            raise ValueError("expected four complete Keccak rounds")
        check_rounds(tmp, expressions, check_schedule(tmp, source))


def check_rounds(tmp, expressions, schedule):
          proofs = ["import Spec.Shake256", "import Std.Tactic.BVDecide", "open Spec.Keccak",
                    "set_option linter.unusedSimpArgs false", "set_option maxRecDepth 8192", "set_option maxHeartbeats 2000000",
                    """private theorem atFn (f : Fin 25 → Lane) (i : Nat) (h : i < 25) :
      (Array.ofFn f)[i]! = f ⟨i,h⟩ := by
    rw [getElem!_pos _ _ (by simpa using h), Array.getElem_ofFn]"""]
          proofs.append(schedule)
          for i, expr in enumerate(expressions):
              w = i % 25
              proofs.append(f"""example (a : State) (c : Lane) : {expr} = (round a c)[{w}]! := by
    simp (disch := decide) only [round, Id.run, pure, atFn, chi, Nat.reduceMod, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, ite_true, ite_false]
    change _ = {projected_round(w)}
    bv_decide""")
          lean = tmp/"Rounds.lean"
          lean.write_text("\n".join(proofs))
          subprocess.run(["lake", "env", "lean", lean], cwd=ROOT/"lean", check=True)


if __name__ == "__main__":
    main()
