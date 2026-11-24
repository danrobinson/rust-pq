import Integration.SlhDsaShakePermutationLongWeights
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The equal-degree harmonic kernel is a positive weighted sum of
coordinate permutations. Its nonidentity part is small in Hilbert-space
operator norm, uniformly over work registers included in the amplitudes. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Finset
noncomputable section
variable {A : Type} [Fintype A] {r : ℕ}

abbrev Index (A : Type) (r : ℕ) := (Fin r → A) × (Fin r → A)
abbrev Space (A : Type) [Fintype A] (r : ℕ) := EuclideanSpace ℂ (Index A r)

def rearrange (u : Equiv.Perm (Fin r)) : Equiv.Perm (Index A r) where
  toFun i := (i.1,i.2 ∘ u.symm)
  invFun i := (i.1,i.2 ∘ u)
  left_inv i := by ext <;> simp [Function.comp_def]
  right_inv i := by ext <;> simp [Function.comp_def]

def move (u : Equiv.Perm (Fin r)) : Space A r ≃ₗᵢ[ℂ] Space A r :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (rearrange u)

theorem move_apply (u : Equiv.Perm (Fin r)) (v : Space A r) (i : Index A r) :
    move u v i = v (i.1,i.2 ∘ u) := rfl

def block (N : ℕ) (H : Finset (Fin r)) (v : Space A r) : Space A r :=
  ∑ u : {u : Equiv.Perm (Fin r) // permutes H u}, (weight N r H.card : ℂ) • move u.val v

theorem norm_block (N : ℕ) (H : Finset (Fin r)) (v : Space A r) :
    ‖block N H v‖ ≤ ((Fintype.card {u : Equiv.Perm (Fin r) // permutes H u} : ℝ) * weight N r H.card) * ‖v‖ := by
  have pos : 0 ≤ weight N r H.card := by unfold weight; positivity
  apply (norm_sum_le _ _).trans
  simp only [norm_smul,LinearIsometryEquiv.norm_map,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc,le_refl]

theorem block_empty (N : ℕ) (v : Space A r) : block N ∅ v = v := by
  let e := Equiv.refl (Fin r)
  have all (u : {u : Equiv.Perm (Fin r) // permutes (∅ : Finset (Fin r)) u}) : u.val = e := by
    apply Equiv.ext; intro i; exact u.property _ (Finset.notMem_empty i)
  have single : Unique {u : Equiv.Perm (Fin r) // permutes (∅ : Finset (Fin r)) u} :=
    ⟨⟨⟨e,fun _ _ => rfl⟩⟩,fun a => Subtype.ext (all a)⟩
  have zero : weight N r 0 = 1 := by simp [weight,Nat.factorial_ne_zero]
  have same : move e v = v := by ext i; rfl
  simp [block,all,same,zero]

theorem near_identity (N : ℕ) (size : 3*r+1 ≤ N) (v : Space A r) :
    ‖(∑ H : Finset (Fin r), block N H v) - v‖ ≤
      ((r : ℝ) * ((r : ℝ)/(N-2*r : ℕ))) * ‖v‖ := by
  have split : (∑ H : Finset (Fin r), block N H v) - v = ∑ H : Finset (Fin r), if H=∅ then 0 else block N H v := by
    have partition (H : Finset (Fin r)) :
        block N H v = (if H=∅ then v else 0) + (if H=∅ then 0 else block N H v) := by
      split <;> simp_all [block_empty]
    conv_lhs => rw [Finset.sum_congr rfl (fun H _ => partition H),Finset.sum_add_distrib]
    simp
  rw [split]
  apply (norm_sum_le _ _).trans
  calc _ ≤ ∑ H : Finset (Fin r), (if H=∅ then 0 else
         (Fintype.card {w : Equiv.Perm (Fin r) // permutes H w} : ℝ) * weight N r H.card) * ‖v‖ := by
         apply Finset.sum_le_sum; intro H _; by_cases h : H=∅
         · simp [h]
         · simpa [h] using norm_block N H v
       _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (total_weight N r size) (norm_nonneg _)

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.near_identity
