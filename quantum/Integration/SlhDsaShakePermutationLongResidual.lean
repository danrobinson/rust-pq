import Integration.SlhDsaShakePermutationClassicalLazy
import Mathlib.Algebra.Group.End

/-! Conditional on a classical table, the remaining uncertainty is exactly
one uniform permutation on the unused input labels. The same completion
answers both directions on the original public port. -/
namespace Reduction.ShakePermutation.Long
open Classical OracleComp PermutationConditioning SetOracle
set_option linter.unusedSectionVars false
noncomputable section
variable {A : Type} [Fintype A] (t : List (A × A)) (ref : Extensions t)
private abbrev free (x : A) := ∀ v ∈ t, x ≠ v.1

def complete (p : Equiv.Perm (UnusedInputs t)) : Extensions t :=
  ⟨(Equiv.Perm.ofSubtype (p := free t) p).trans ref.val,by
    intro e mem
    have fixed : ¬ free t e.1 := fun h => h e mem rfl
    simp only [Equiv.trans_apply,Equiv.Perm.ofSubtype_apply_of_not_mem _ fixed,ref.property e mem]⟩

private def gap (π : Extensions t) := π.val.trans ref.val.symm

private theorem fixed (π : Extensions t) (x : A) (mem : ¬ free t x) : gap t ref π x = x := by
  classical
  unfold free at mem
  push Not at mem
  obtain ⟨e,mem,eq⟩ := mem
  change ref.val.symm (π.val x) = x
  rw [eq,π.property e mem,← ref.property e mem,Equiv.symm_apply_apply]

private theorem preserves (π : Extensions t) (x : A) : free t (gap t ref π x) ↔ free t x := by
  constructor
  · intro hy e he hx
    have old : ¬ free t x := fun h => h e he hx
    rw [fixed t ref π x old] at hy
    exact old hy
  · intro hx e he h
    have old : ¬ free t e.1 := fun k => k e he rfl
    exact hx e he ((gap t ref π).injective (h.trans (fixed t ref π e.1 old).symm))

def residualEquiv : Equiv.Perm (UnusedInputs t) ≃ Extensions t where
  toFun := complete t ref
  invFun π := Equiv.Perm.subtypePerm (gap t ref π) (preserves t ref π)
  left_inv p := by
    apply Equiv.ext; intro x
    apply Subtype.ext
    change ref.val.symm (ref.val (Equiv.Perm.ofSubtype (p := free t) p x.val)) = _
    rw [Equiv.symm_apply_apply,Equiv.Perm.ofSubtype_apply_of_mem _ x.property]
  right_inv π := by
    apply Subtype.ext
    apply Equiv.ext; intro x
    change ref.val (Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm (gap t ref π) (preserves t ref π)) x) = π.val x
    by_cases hx : free t x
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
      exact ref.val.apply_symm_apply _
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]
      exact (congrArg ref.val (fixed t ref π x hx)).symm.trans (ref.val.apply_symm_apply _)

theorem residual_mean (W : Extensions t → ENNReal) :
    uniformMean (fun p => W (complete t ref p)) = uniformMean W := by
  let e := residualEquiv t ref
  have h := Equiv.sum_comp e (fun p => unifW _ p * W p)
  have act (p) : e p = complete t ref p := rfl
  simpa only [uniformMean,unifW,Fintype.card_congr e,act] using h

theorem forward_unused (p : Equiv.Perm (UnusedInputs t)) (x : UnusedInputs t) :
    (complete t ref p).val x.val = ref.val (p x).val := by
  change ref.val (Equiv.Perm.ofSubtype (p := free t) p x.val) = _
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ x.property]

theorem inverse_unused (p : Equiv.Perm (UnusedInputs t)) (x : UnusedInputs t) :
    (complete t ref p).val.symm (ref.val x.val) = (p.symm x).val := by
  apply (complete t ref p).val.injective
  rw [Equiv.apply_symm_apply,forward_unused,Equiv.apply_symm_apply]

end
end Reduction.ShakePermutation.Long
#print axioms Reduction.ShakePermutation.Long.residual_mean
