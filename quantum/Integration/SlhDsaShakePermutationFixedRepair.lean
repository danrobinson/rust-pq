import Integration.SlhDsaShakePermutationRelabel
import VCVio.Quantum.Oracle.Compressed.Oracle

/-! A relabeling controlled by the *decompressed* mask database intertwines full
compressed mask queries exactly. The concrete pairing below registers a fixed
intermediate address, a fixed entering capacity, and a fixed path. -/
namespace Reduction.ShakePermutation.FixedRepair
open Classical Quantum Matrix
open scoped Kronecker
variable {X Y B : Type} [Fintype X] [Fintype Y] [Fintype B]
  [DecidableEq X] [DecidableEq Y] [DecidableEq B] [AddCommGroup Y]

abbrev Joint (X Y B : Type) := ((X × Y) × Database X Y) × B
abbrev Square (T : Type) := Matrix T T ℂ

def raw (v : Database X Y → Equiv.Perm B) : Equiv.Perm (Joint X Y B) where
  toFun s := (s.1,v s.1.2 s.2)
  invFun s := (s.1,(v s.1.2).symm s.2)
  left_inv s := by simp
  right_inv s := by simp

noncomputable def changeBasis : Square (Joint X Y B) :=
  ((1 : Square (X × Y)) ⊗ₖ compressAll X Y) ⊗ₖ (1 : Square B)

noncomputable def repair (v : Database X Y → Equiv.Perm B) : Square (Joint X Y B) :=
  changeBasis * basisMatrix (raw v) * changeBasis

private theorem change_sq : (changeBasis : Square (Joint X Y B)) * changeBasis = 1 := by
  rw [changeBasis, ← mul_kronecker_mul, one_kronecker_compressAll_mul_self, one_mul,
    one_kronecker_one]

omit [Fintype B] [AddCommGroup Y] in
private theorem change_star : (changeBasis : Square (Joint X Y B))ᴴ = changeBasis := by
  rw [changeBasis, conjTranspose_kronecker, conjTranspose_one_kronecker_compressAll,
    conjTranspose_one]

private theorem standard_commutes (v : Database X Y → Equiv.Perm B) :
    basisMatrix (raw v) * (standardOracle X Y ⊗ₖ (1 : Square B)) =
    (standardOracle X Y ⊗ₖ (1 : Square B)) * basisMatrix (raw v) := by
  rw [standardOracle,tableOracle,basisMatrix_kronecker_one, ← basisMatrix_comp,
    ← basisMatrix_comp]
  rfl

private theorem query_conjugation :
    compressedOracle X Y ⊗ₖ (1 : Square B) =
      changeBasis * (standardOracle X Y ⊗ₖ (1 : Square B)) * changeBasis := by
  simp only [changeBasis, ← mul_kronecker_mul, one_mul, compressedOracle]

theorem repair_on_decompressed (v : Database X Y → Equiv.Perm B) :
    repair v * changeBasis = changeBasis * basisMatrix (raw v) := by
  rw [repair, Matrix.mul_assoc _ changeBasis, change_sq, Matrix.mul_one]

theorem repair_unitary (v : Database X Y → Equiv.Perm B) :
    (repair v)ᴴ * repair v = 1 := by
  simp only [repair, conjTranspose_mul, change_star, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc changeBasis changeBasis, change_sq, Matrix.one_mul,
    ← Matrix.mul_assoc (basisMatrix (raw v))ᴴ (basisMatrix (raw v)),
    conjTranspose_basisMatrix_mul_self (raw v).injective]

theorem repair_commutes (v : Database X Y → Equiv.Perm B) :
    repair v * (compressedOracle X Y ⊗ₖ (1 : Square B)) =
      (compressedOracle X Y ⊗ₖ (1 : Square B)) * repair v := by
  rw [query_conjugation, repair]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc changeBasis changeBasis,
    change_sq, Matrix.one_mul]
  rw [← Matrix.mul_assoc (basisMatrix (raw v)) _ changeBasis, standard_commutes,
    Matrix.mul_assoc]

open Relabel Tails

noncomputable def mark {L : ℕ} (z : Capacity) (p : Path L) (h : Rate)
    (d : Cells L) : Cells L
  | .inl w => if w = z then twist h (d (.inr p)) else d (.inl w)
  | .inr q => if q = p then twist h (d (.inl z)) else d (.inr q)

theorem mark_involutive {L : ℕ} (z : Capacity) (p : Path L) (h : Rate) :
    Function.Involutive (mark z p h) := by
  intro d
  funext i
  cases i with
  | inl w => by_cases e : w = z <;> simp [mark,e]
  | inr q => by_cases e : q = p <;> simp [mark,e]

noncomputable def fixedParent {L : ℕ} (a : Rate) (c : Capacity) (p : Path L) (h : Rate)
    (db : Database (Bool × Rate) Capacity) : Equiv.Perm (Cells L) :=
  match db (true,a) with
  | none => Equiv.refl _
  | some y => (mark_involutive (xorCap c y) p h).toPerm _

theorem fixedParent_reads {L : ℕ} (a : Rate) (c y : Capacity) (p : Path L) (h : Rate)
    (db : Database (Bool × Rate) Capacity) (d : Cells L) (hy : db (true,a) = some y) :
    fixedParent a c p h db d (.inr p) = twist h (d (.inl (xorCap c y))) ∧
    fixedParent a c p h db d (.inl (xorCap c y)) = twist h (d (.inr p)) := by
  simp only [fixedParent,hy]
  simp [Function.Involutive.toPerm, mark]

set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable local instance (L : ℕ) : Fintype (Cells L) := by
  classical
  letI : Fintype (Capacity ⊕ Path L) := inferInstance
  unfold Cells
  infer_instance

/-- The coherent two-bank query may select either mask and any address. -/
theorem fixedParent_commutes {L : ℕ} (a : Rate) (c : Capacity) (p : Path L) (h : Rate) :
    repair (fixedParent a c p h) *
        (compressedOracle (Bool × Rate) Capacity ⊗ₖ (1 : Square (Cells L))) =
      (compressedOracle (Bool × Rate) Capacity ⊗ₖ (1 : Square (Cells L))) *
        repair (fixedParent a c p h) :=
  repair_commutes _

end Reduction.ShakePermutation.FixedRepair
#print axioms Reduction.ShakePermutation.FixedRepair.fixedParent_commutes
#print axioms Reduction.ShakePermutation.FixedRepair.repair_unitary
