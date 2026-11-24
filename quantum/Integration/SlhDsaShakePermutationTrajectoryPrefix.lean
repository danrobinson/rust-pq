import Integration.SlhDsaShakePermutationTrajectoryTypical

namespace Reduction.ShakePermutation.MsgTrajectory.Risk
open Classical SetOracle ENNReal
noncomputable section
set_option maxRecDepth 8192
variable {A : Type} [DecidableEq A]

theorem returns_append (π : Equiv.Perm A) (s x : A) (bs more : List (Equiv.Perm A)) :
    returns π s x bs = true → returns π s x (bs ++ more) = true := by
  induction bs generalizing x with
  | nil => cases more <;> simp [returns] <;> exact Or.inl
  | cons b bs ih =>
    simp only [List.cons_append,returns,Bool.or_eq_true]
    exact Or.imp id (ih _)

private theorem fill (b : Rate) (bs : List Rate) (len : bs.length ≤ 482) :
    ∃ v : Blocks, v 0 = b ∧ ∃ more, next v = bs.map absorbBlock ++ more := by
  let xs := bs ++ List.replicate (482-bs.length) (0 : Rate)
  have length : xs.length = 482 := by simp [xs]; omega
  let v : Blocks := Fin.cases b (fun i => xs[i.val]'(by rw [length]; exact i.isLt))
  refine ⟨v,rfl,(List.replicate (482-bs.length) (0 : Rate)).map absorbBlock,?_⟩
  have eq : next v = xs.map absorbBlock := by
    apply List.ext_getElem
    · simp only [next,List.length_ofFn,List.length_map,length]
    · intro i h₁ h₂; simp only [next,List.getElem_ofFn,List.getElem_map,v,Fin.cases_succ]
  rw [eq]; exact List.map_append

private theorem mass_mono [Fintype A] (π g : Equiv.Perm A) (bs more : List (Equiv.Perm A)) :
    mass π g bs ≤ mass π g (bs ++ more) := by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul' le_rfl
  dsimp only
  by_cases ev : returns π s (g s) bs = true
  · rw [ite_eq_left ev,ite_eq_left (returns_append π s _ _ more ev)]
  · rw [ite_eq_right ev]; exact zero_le
set_option allowUnsafeReducibility true in
attribute [local irreducible] mass next

theorem return_risk (π : Permutation) (typical : ¬exceptional π) (b : Rate) (bs : List Rate)
    (len : bs.length ≤ 482) : mass π (absorbBlock b) (bs.map absorbBlock) ≤ ((2:ℝ≥0∞)^400)⁻¹ := by
  obtain ⟨v,hb,more,eq⟩ := fill b bs len
  have lim : (2:ℝ≥0∞)^400 * mass π (absorbBlock (v 0)) (next v) ≤ 1 :=
    le_of_lt (lt_of_not_ge fun large => typical ⟨v,large⟩)
  have mono : mass π (absorbBlock b) (bs.map absorbBlock) ≤ mass π (absorbBlock (v 0)) (next v) := by
    rw [hb,eq]
    exact mass_mono _ _ _ _
  apply mono.trans
  calc _ = ((2:ℝ≥0∞)^400)⁻¹ * ((2:ℝ≥0∞)^400 * mass π (absorbBlock (v 0)) (next v)) := by
              rw [← mul_assoc,ENNReal.inv_mul_cancel (by positivity) (by finiteness),one_mul]
       _ ≤ _ := by simpa only [mul_one] using mul_le_mul' (le_refl (((2:ℝ≥0∞)^400)⁻¹)) lim

end
end Reduction.ShakePermutation.MsgTrajectory.Risk
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.return_risk
