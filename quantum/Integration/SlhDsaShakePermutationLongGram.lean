import Integration.SlhDsaShakePermutationLongResidual
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Completion vectors for partial permutation matchings. Their overlaps
are exactly zero for inconsistent matchings and a factorial ratio for
compatible matchings, including repeated edges in the descriptions. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical OracleComp PermutationConditioning Classic Finset
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Trace (A : Type) := List (A × A)

def inputs (t : Trace A) : Finset A := (t.map Prod.fst).toFinset

def rank (t : Trace A) := (inputs t).card

def agrees (t : Trace A) (π : Equiv.Perm A) : Prop := ∀ e ∈ t, π e.1 = e.2

theorem unused_count (t : Trace A) : Fintype.card (UnusedInputs t) = Fintype.card A - rank t := by
  classical
  have eq (x : A) : (∀ p ∈ t, x ≠ p.1) ↔ x ∈ (inputs t)ᶜ := by
    simp only [inputs,Finset.mem_compl,List.mem_toFinset,List.mem_map,not_exists]
    grind
  let E : UnusedInputs t ≃ ↥(inputs t)ᶜ := Equiv.subtypeEquivRight eq
  rw [Fintype.card_congr E,Fintype.card_coe,Finset.card_compl,rank]

theorem extension_count (t : Trace A) (ok : Nonempty (Extensions t)) :
    Fintype.card (Extensions t) = (Fintype.card A - rank t).factorial := by
  classical
  rw [← Fintype.card_congr (Long.residualEquiv t ok.some),Fintype.card_perm,unused_count]

def count (t : Trace A) := if Nonempty (Extensions t) then (Fintype.card A - rank t).factorial else 0

theorem count_eq (t : Trace A) : Fintype.card (Extensions t) = count t := by
  classical
  by_cases h : Nonempty (Extensions t)
  · rw [count,ite_eq_left h,extension_count t h]
  · have := not_nonempty_iff.mp h
    simp [count,h]

def indicator (t : Trace A) (π : Equiv.Perm A) : ℝ := if agrees t π then 1 else 0

omit [Fintype A] [DecidableEq A] in
theorem indicator_mul (t u : Trace A) (π : Equiv.Perm A) :
    indicator t π * indicator u π = indicator (t ++ u) π := by
  have union : agrees (t++u) π ↔ agrees t π ∧ agrees u π := by
    simp only [agrees,List.mem_append,or_imp,forall_and]
  by_cases ht : agrees t π <;> by_cases hu : agrees u π <;> simp [indicator,union,ht,hu]

theorem indicator_sum (t : Trace A) : ∑ π, indicator t π = (count t : ℝ) := by
  classical
  rw [← count_eq]
  simp only [indicator,Finset.sum_boole]
  rw [← Fintype.card_subtype (agrees t)]
  apply congrArg Nat.cast
  apply Fintype.card_congr
  exact Equiv.refl _

/-- Normalizing each nonzero indicator gives the unit extension state. -/
def vector (t : Trace A) (π : Equiv.Perm A) : ℝ := indicator t π / Real.sqrt (count t)

theorem overlap (t u : Trace A) :
    ∑ π, vector t π * vector u π =
      (count (t++u) : ℝ) / (Real.sqrt (count t) * Real.sqrt (count u)) := by
  simp only [vector,div_mul_div_comm,indicator_mul,← Finset.sum_div,indicator_sum]

theorem overlap_self (t : Trace A) (ok : Nonempty (Extensions t)) :
    ∑ π, vector t π * vector t π = 1 := by
  have same : count (t++t) = count t := by
    rw [← count_eq,← count_eq]
    exact Fintype.card_congr (extensionsEquivOfMemIff _ _ (by simp))
  have h : count t ≠ 0 := by rw [count,ite_eq_left ok]; exact Nat.factorial_ne_zero _
  rw [overlap,same,Real.mul_self_sqrt (Nat.cast_nonneg _),div_self (Nat.cast_ne_zero.mpr h)]

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.overlap
