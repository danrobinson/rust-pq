import Integration.SlhDsaShakePermutationLongHarmonic

/-! Two-coordinate estimate for harmonic projection on ordered
injections. Conditioning on all other coordinates leaves two distinct
labels in a finite alphabet. Averaging a centered one-label function over
the labels allowed by the other coordinate negates its missing value. -/
namespace Reduction.ShakePermutation.Long.Harmonic
open Finset Complex
open scoped ComplexConjugate
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]

theorem missing (f : A → ℂ) (hf : ∑ a, f a = 0) (a : A) :
    ∑ b ∈ univ.erase a, f b = -f a := by
  exact eq_neg_of_add_eq_zero_left ((Finset.sum_erase_add _ _ (Finset.mem_univ a)).trans hf)

def cross (f g : A → ℂ) : ℝ := ∑ a, ∑ b ∈ univ.erase a, (f a * conj (g b)).re

theorem cross_eq (f g : A → ℂ) (hg : ∑ b, g b = 0) :
    cross f g = -∑ a, (f a * conj (g a)).re := by
  classical
  unfold cross; rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro a _
  have he : ∑ b ∈ univ.erase a, f a * conj (g b) = -(f a * conj (g a)) := by
    rw [← Finset.mul_sum,← map_sum,missing g hg,map_neg,mul_neg]
  simpa only [Complex.re_sum,Complex.neg_re] using congrArg Complex.re he

theorem approx_orthogonal (f g : A → ℂ) (hg : ∑ b, g b = 0) :
    -∑ a, (normSq (f a) + normSq (g a)) ≤ 2 * cross f g := by
  rw [cross_eq f g hg,mul_neg,neg_le_neg_iff,Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    have diff := normSq_nonneg (f a - g a)
    rw [normSq_sub] at diff
    linarith

theorem slice_energy (f g : A → ℂ) (hg : ∑ b, g b = 0) :
    ((Fintype.card A : ℝ) - 2) * (∑ a, (normSq (f a) + normSq (g a))) ≤
      ∑ a, ∑ b ∈ univ.erase a, normSq (f a + g b) := by
  classical
  have centered := approx_orthogonal f g hg
  have nz : Nonempty A ∨ IsEmpty A := Classical.em _ |>.imp_right not_nonempty_iff.mp
  rcases nz with nonempty|empty
  · have := nonempty
    have k : ∀ a : A, ((univ.erase a).card : ℝ) = Fintype.card A - 1 := fun a => by
      rw [card_erase_of_mem (mem_univ a),card_univ,Nat.cast_sub (Fintype.card_pos_iff.mpr nonempty),Nat.cast_one]
    have swap_sum (v : A → ℝ) : ∑ a, ∑ b ∈ univ.erase a, v b = (Fintype.card A - 1 : ℝ) * ∑ a, v a := by
      have exchange : ∀ a : A, ∑ b ∈ univ.erase a, v b = ∑ b, if b = a then 0 else v b :=
        fun a => by rw [Finset.sum_ite,Finset.sum_const_zero,zero_add]; congr 1; ext b; simp [ne_comm]
      simp only [exchange]; rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,nsmul_eq_mul]
      congr 1
      simpa only [Finset.filter_ne] using k a
    simp only [normSq_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,k]
    rw [← Finset.mul_sum,swap_sum]
    unfold cross at centered
    simp only [← Finset.mul_sum] at *
    rw [Finset.sum_add_distrib] at centered
    nlinarith
  · have := empty; simp

end
end Reduction.ShakePermutation.Long.Harmonic
#print axioms Reduction.ShakePermutation.Long.Harmonic.slice_energy
