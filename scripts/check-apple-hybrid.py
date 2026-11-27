#!/usr/bin/env python3
"""Lift the production hybrid Keccak rounds to bitvectors and check them against FIPS 202."""
from pathlib import Path
import argparse
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
    neon = "    pub(super) unsafe fn permute_active" + neon.split("\n}", 1)[0]
    def module(name, body):
        body = re.sub(r'#\[target_feature\(enable = "[^"]+"\)\]', '', body)
        body = body.replace("[u64; 25]", "[Word; 25]")
        body = body.replace("unsafe { vld1q_u64(words[i].as_ptr().add(off)) }",
                            "[words[i][off], words[i][off+1]]")
        body = body.replace("unsafe { vst1q_u64(words[i].as_mut_ptr().add(off), a[i]) }",
                            "words[i][off..off+2].copy_from_slice(&a[i])")
        return "mod " + name + " { use super::*; use super::round_" + name + " as round;\n" + body + "}\n"
    rc = re.search(r"const RC: \[u64; 24\] = \[(.*?)\];",
                   (ROOT/"rust/src/shake256.rs").read_text(), re.S)
    probe = (HERE/"schedule.rs").read_text().replace("// ROUND_CONSTANTS", rc[0])
    dispatch = source[source.index("pub(crate) fn available()"):source.index("pub(super) fn single(state:")]
    dispatch = dispatch[:dispatch.rindex("#[cfg")]
    for original in ("target_arch", "target_vendor", "target_feature"):
        dispatch = dispatch.replace(original, "lift_" + original)
    probe = probe.replace("// PRODUCTION", module("sha3", sha3) + module("neon", neon) + dispatch)
    (tmp/"schedule.rs").write_text(probe)
    subprocess.run(["rustc", tmp/"schedule.rs", "--cfg", 'lift_target_arch="aarch64"',
                    "--cfg", 'lift_target_vendor="apple"', "--cfg", 'lift_target_feature="neon"',
                    "-o", tmp/"schedule"], check=True)
    rows = subprocess.check_output([tmp/"schedule"], text=True).splitlines()
    rounds, tables = {}, {}
    for row in rows:
        n, sha3_enabled, lane, source_lane, *calls = row.split()
        seq = tuple(calls)
        idx = rounds.setdefault(seq, len(rounds))
        table = tables.setdefault((int(n), int(sha3_enabled)), [])
        if int(lane) != len(table):
            raise ValueError("incomplete or unordered lane trace")
        table.append(f"({source_lane}, program{idx})")
    if len(tables) != 20 or any(len(row) != 8 for row in tables.values()):
        raise ValueError("incomplete Apple dispatch")
    parts = ["""-- Generated from the Apple dispatch and row load/store loops by scripts/check-apple-hybrid.py.
import Cachepath.AppleHybridRounds
namespace slhdsa.AppleHybrid
open Spec.Keccak
abbrev Route := Fin 8 × List (Kind × Lane)
"""]
    for seq, idx in rounds.items():
        calls = [token.split(":") for token in seq]
        program = ", ".join(f"(.{kind}, {hex(int(c))})" for kind, c in calls)
        parts.append(f"private def program{idx} : List (Kind × Lane) := [{program}]")
    parts += ["", "/-- Dispatch indices 0–8 call permute_active; index 9 calls permute. -/",
              "def schedule (n : Fin 10) (sha3 : Bool) : _root_.Array Route :=",
              "  match n.val, sha3 with"]
    for (n, sha3_enabled), table in tables.items():
        enabled = str(bool(sha3_enabled)).lower()
        parts.append(f"  | {n}, {enabled} => #[{', '.join(table)}]")
    parts += ["  | _, _ => #[]", "", "end slhdsa.AppleHybrid", ""]
    return "\n".join(parts)


def round_program(expressions):
    names = ["scalar", "inplace", "sha3", "neon"]
    parts = ["""-- Generated from rust/src/shake256/parallel.rs by scripts/check-apple-hybrid.py.
import Spec.ShakeWords
import Mathlib.Tactic.IntervalCases
open Spec.Keccak
namespace slhdsa.AppleHybrid
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

inductive Kind | scalar | inplace | sha3 | neon deriving DecidableEq, Inhabited

private theorem rotzero (x : Lane) : x.rotateLeft 0 = x := by
  simp [BitVec.rotateLeft_def, BitVec.ushiftRight_eq_zero]

private theorem shiftRotate (x : Lane) (l r : Nat) (h : l < 64) (hr : r = 64-l) :
    ((x <<< l) &&& ((-1 : Lane) <<< l)) ||| (x >>> r) = x.rotateLeft l := by
  change ((x <<< l) &&& (BitVec.allOnes 64 <<< l)) ||| _ = _
  rw [← BitVec.shiftLeft_and_distrib, BitVec.and_allOnes]
  simp [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h, hr]
"""]
    for k, name in enumerate(names):
        cells = [f"{name}{w}" for w in range(25)]
        for w, cell_name in enumerate(cells):
            expr = expressions[25*k+w]
            parts.append(f"""private def {cell_name} (a : State) (c : Lane) : Lane := {expr}
private theorem {cell_name}_eq (a : State) (c : Lane) : {cell_name} a c = (round a c)[{w}]! := by
  rw [roundAt _ _ _ (by decide)]
  change {cell_name} a c = {projected_round(w)}
  simp (disch := decide) only [{cell_name}, shiftRotate, rotzero] <;> ac_rfl
""")
        vector = ", ".join(x + " a c" for x in cells)
        cases = "\n".join("  · exact "+x+"_eq a c" for x in cells)
        parts.append(f"""def {name}Round (a : State) (c : Lane) : State := #[{vector}]
private theorem {name}_eq (a : State) (c : Lane) : {name}Round a c = round a c := by
  apply ext25 _ _ rfl (by simp [round])
  intro i hi
  interval_cases i
{cases}
""")
    parts += ["""def liftedRound : Kind → State → Lane → State
  | .scalar => scalarRound
  | .inplace => inplaceRound
  | .sha3 => sha3Round
  | .neon => neonRound

theorem liftedRound_eq (k : Kind) (a : State) (c : Lane) :
    liftedRound k a c = round a c := by
  cases k <;> first | apply scalar_eq | apply inplace_eq | apply sha3_eq | apply neon_eq

end slhdsa.AppleHybrid
"""]
    return "\n".join(parts)


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"), str(Path.home()/".cargo/bin"), os.environ["PATH"]])
    parser = argparse.ArgumentParser()
    parser.add_argument("--refresh", action="store_true", help="regenerate the source projections")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        source = SRC.read_text()
        probe = (HERE / "rounds.rs").read_text().replace("// PRODUCTION", lift_rounds(source))
        (tmp / "rounds.rs").write_text(probe)
        subprocess.run(["rustc", tmp/"rounds.rs", "-o", tmp/"rounds"], check=True)
        expressions = subprocess.check_output([tmp/"rounds"], text=True).splitlines()
        if len(expressions) != 100:
            raise ValueError("expected four complete Keccak rounds")
        projected = { "AppleHybridRounds": round_program(expressions),
                      "AppleHybridSchedule": check_schedule(tmp, source) }
        for name, content in projected.items():
            path = ROOT/"lean-hw"/"Cachepath"/(name+".lean")
            if args.refresh:
                path.write_text(content)
            elif path.read_text() != content:
                raise ValueError(f"{path} differs from the production source lift")
        subprocess.run(["lake", "build", "Cachepath.AppleHybrid"], cwd=ROOT/"lean-hw", check=True)
        proof = "import Cachepath.AppleHybrid\n#print axioms slhdsa.AppleHybrid.permutation_correct\n"
        out = subprocess.check_output(["lake", "env", "lean", "--stdin"], input=proof,
                                      cwd=ROOT/"lean-hw", text=True)
        axioms = re.search(r"depends on axioms: \[(.*?)\]", out)
        if not axioms or set(axioms[1].split(", ")) - {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError(out)
        print(out.strip())


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
