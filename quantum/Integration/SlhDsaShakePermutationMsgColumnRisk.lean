import Integration.SlhDsaShakePermutationMsgImage

namespace Reduction.ShakePermutation.MsgTrajectory.Risk
open Classical SetOracle ENNReal
noncomputable section
variable {A J : Type} [Fintype A] [DecidableEq A] [Fintype J]

def marked (u : J ↪ A) (x : A) (π σ g : Equiv.Perm A) : Prop :=
  (∃ j, g (σ x) = u j) ∨ (∃ j, u j ≠ x ∧ σ (u j) = π (g (σ x)))

theorem union_avg {X : Type} [Fintype X] (e : X → J → Prop) [DecidableRel e]
    (b : ℝ≥0∞) (each : ∀ j, uniformMean (fun z => if e z j then (1:ℝ≥0∞) else 0) ≤ b) :
    uniformMean (fun z => if ∃ j, e z j then (1:ℝ≥0∞) else 0) ≤ Fintype.card J * b := by
  classical
  have p (z : X) : (if ∃ j, e z j then (1:ℝ≥0∞) else 0) ≤ ∑ j, if e z j then 1 else 0 := by
    split
    · rename_i h
      obtain ⟨j,hj⟩ := h
      exact (ite_eq_left hj).ge.trans (Finset.single_le_sum (f:=fun j => if e z j then (1:ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ j))
    · exact zero_le
  apply (Finset.sum_le_sum (s:=Finset.univ) fun z _ => mul_le_mul' (le_rfl : unifW X z ≤ _) (p z)).trans
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact (Finset.sum_le_sum (s:=Finset.univ) fun j _ => each j).trans_eq (by simp [nsmul_eq_mul])

theorem marked_step (u : J ↪ A) (x : A) (π g : Equiv.Perm A) :
    uniformMean (fun σ : Equiv.Perm A => if marked u x π σ g then (1:ℝ≥0∞) else 0) ≤
      (Fintype.card J : ℝ≥0∞)*(1/Fintype.card A) + (Fintype.card J : ℝ≥0∞)*(1/((Fintype.card A-1:ℕ):ℝ≥0∞)) := by
  classical
  let left (σ : Equiv.Perm A) (j : J) := g (σ x) = u j
  let right (σ : Equiv.Perm A) (j : J) := u j ≠ x ∧ σ (u j) = π (g (σ x))
  have first (j : J) : uniformMean (fun σ => if left σ j then (1:ℝ≥0∞) else 0) ≤ 1/Fintype.card A := by
    change uniformMean (fun σ : Equiv.Perm A => (fun a => if g a = u j then (1:ℝ≥0∞) else 0) (σ x)) ≤ _
    apply (random_image x (fun a => if g a = u j then (1:ℝ≥0∞) else 0)).le.trans
    apply (Classic.mean_equiv g (fun a => if a = u j then (1:ℝ≥0∞) else 0)).le.trans
    simp [uniformMean,unifW,mul_ite]
  have next (j : J) : uniformMean (fun σ => if right σ j then (1:ℝ≥0∞) else 0) ≤ 1/((Fintype.card A-1:ℕ):ℝ≥0∞) := by
    by_cases h : u j = x
    · simp [right,h,uniformMean]
    · simpa only [right,and_iff_right h] using second_image x (u j) h (fun a => π (g a))
  have per (σ : Equiv.Perm A) : (if marked u x π σ g then (1:ℝ≥0∞) else 0) ≤
      (if ∃ j, left σ j then 1 else 0) + (if ∃ j, right σ j then 1 else 0) := by
    have iff : marked u x π σ g ↔ (∃ j, left σ j) ∨ (∃ j, right σ j) := Iff.rfl
    simp only [iff]
    by_cases h : ∃ j, left σ j <;> by_cases k : ∃ j, right σ j <;> simp [h,k]
  apply (Finset.sum_le_sum (s:=Finset.univ) fun σ _ => mul_le_mul' (le_rfl : unifW _ σ ≤ _) (per σ)).trans
  simp only [mul_add,Finset.sum_add_distrib]
  exact add_le_add (union_avg left _ first) (union_avg right _ next)

end
end Reduction.ShakePermutation.MsgTrajectory.Risk
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.marked_step
