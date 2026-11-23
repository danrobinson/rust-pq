import Mathlib.Tactic.IntervalCases
import Spec.Shake256
open Spec.Keccak
namespace slhdsa.Oriented
private theorem rotbit (a : Lane) (r i : Nat) (hi : i < 64) :
    (a.rotateLeft r)[i] = a[(i+64-r%64)%64]'(by omega) := by
  rw [BitVec.getElem_rotateLeft]
  split <;> congr 1 <;> omega

theorem chi0 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 1)).rotateLeft 43).rotateLeft 0 =
      x.rotateLeft 0 ^^^ ((~~~(y.rotateLeft 44)) &&& z.rotateLeft 43) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi1 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 22)).rotateLeft 41).rotateLeft 44 =
      x.rotateLeft 44 ^^^ ((~~~(y.rotateLeft 43)) &&& z.rotateLeft 21) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi2 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 7)).rotateLeft 35).rotateLeft 43 =
      x.rotateLeft 43 ^^^ ((~~~(y.rotateLeft 21)) &&& z.rotateLeft 14) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi3 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 14)).rotateLeft 43).rotateLeft 21 =
      x.rotateLeft 21 ^^^ ((~~~(y.rotateLeft 14)) &&& z.rotateLeft 0) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi4 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 20)).rotateLeft 30).rotateLeft 14 =
      x.rotateLeft 14 ^^^ ((~~~(y.rotateLeft 0)) &&& z.rotateLeft 44) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi5 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 17)).rotateLeft 39).rotateLeft 28 =
      x.rotateLeft 28 ^^^ ((~~~(y.rotateLeft 20)) &&& z.rotateLeft 3) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi6 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 22)).rotateLeft 25).rotateLeft 20 =
      x.rotateLeft 20 ^^^ ((~~~(y.rotateLeft 3)) &&& z.rotateLeft 45) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi7 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 48)).rotateLeft 58).rotateLeft 3 =
      x.rotateLeft 3 ^^^ ((~~~(y.rotateLeft 45)) &&& z.rotateLeft 61) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi8 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 33)).rotateLeft 47).rotateLeft 45 =
      x.rotateLeft 45 ^^^ ((~~~(y.rotateLeft 61)) &&& z.rotateLeft 28) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi9 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 8)).rotateLeft 23).rotateLeft 61 =
      x.rotateLeft 61 ^^^ ((~~~(y.rotateLeft 28)) &&& z.rotateLeft 20) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi10 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 45)).rotateLeft 24).rotateLeft 1 =
      x.rotateLeft 1 ^^^ ((~~~(y.rotateLeft 6)) &&& z.rotateLeft 25) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi11 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 17)).rotateLeft 2).rotateLeft 6 =
      x.rotateLeft 6 ^^^ ((~~~(y.rotateLeft 25)) &&& z.rotateLeft 8) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi12 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 54)).rotateLeft 57).rotateLeft 25 =
      x.rotateLeft 25 ^^^ ((~~~(y.rotateLeft 8)) &&& z.rotateLeft 18) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi13 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 17)).rotateLeft 57).rotateLeft 8 =
      x.rotateLeft 8 ^^^ ((~~~(y.rotateLeft 18)) &&& z.rotateLeft 1) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi14 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 59)).rotateLeft 52).rotateLeft 18 =
      x.rotateLeft 18 ^^^ ((~~~(y.rotateLeft 1)) &&& z.rotateLeft 6) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi15 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 26)).rotateLeft 47).rotateLeft 27 =
      x.rotateLeft 27 ^^^ ((~~~(y.rotateLeft 36)) &&& z.rotateLeft 10) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi16 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 59)).rotateLeft 43).rotateLeft 36 =
      x.rotateLeft 36 ^^^ ((~~~(y.rotateLeft 10)) &&& z.rotateLeft 15) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi17 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 23)).rotateLeft 46).rotateLeft 10 =
      x.rotateLeft 10 ^^^ ((~~~(y.rotateLeft 15)) &&& z.rotateLeft 56) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi18 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 29)).rotateLeft 12).rotateLeft 15 =
      x.rotateLeft 15 ^^^ ((~~~(y.rotateLeft 56)) &&& z.rotateLeft 27) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi19 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 55)).rotateLeft 44).rotateLeft 56 =
      x.rotateLeft 56 ^^^ ((~~~(y.rotateLeft 27)) &&& z.rotateLeft 36) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi20 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 16)).rotateLeft 41).rotateLeft 62 =
      x.rotateLeft 62 ^^^ ((~~~(y.rotateLeft 55)) &&& z.rotateLeft 39) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi21 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 62)).rotateLeft 50).rotateLeft 55 =
      x.rotateLeft 55 ^^^ ((~~~(y.rotateLeft 39)) &&& z.rotateLeft 41) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi22 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 39)).rotateLeft 27).rotateLeft 39 =
      x.rotateLeft 39 ^^^ ((~~~(y.rotateLeft 41)) &&& z.rotateLeft 2) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi23 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 4)).rotateLeft 21).rotateLeft 41 =
      x.rotateLeft 41 ^^^ ((~~~(y.rotateLeft 2)) &&& z.rotateLeft 62) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

theorem chi24 (x y z : Lane) :
    (x ^^^ (z &&& ~~~(y.rotateLeft 7)).rotateLeft 53).rotateLeft 2 =
      x.rotateLeft 2 ^^^ ((~~~(y.rotateLeft 62)) &&& z.rotateLeft 55) := by
  ext i hi
  simp only [rotbit, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not, Bool.and_comm]
  interval_cases i <;> rfl

end slhdsa.Oriented
