import Integration.SlhDsaShakePermutationLongTargetGrowth

/-! Classical graph-failure probability for each newly sampled private row.
The rate bank does not change the capacity graph. -/
namespace Reduction.ShakePermutation.Long.BankRun
open Classical Tails MLink Quantum OracleSpec ENNReal SetOracle ItsrLabel
noncomputable section
set_option maxRecDepth 11000
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support badLeft badRight uniformMean Fintype.card

def graphClean (π : Permutation) (D : Bank) := Graph.Good (layout π) (masks D false) (masks D true)
def graphRate (Q : ℕ) : ℝ≥0∞ := (extensionBudget Q : ℝ≥0∞) / Fintype.card Capacity

theorem graph_empty (π : Permutation) : graphClean π (fun _ => none) := Graph.good_empty _

private theorem cap_failure (p : Words → Prop) [DecidablePred p] (b : Finset Capacity) (t : ℕ)
    (im : ∀ w, p w → capOf w ∈ b) (cnt : b.card ≤ extensionBudget t) :
    uniformMean (fun w : Words => Classic.hit (p w)) ≤ graphRate t := by
  apply (conditional p (fun w : Words => capOf w ∈ b) im).trans
  rw [cap_mean (fun v => Classic.hit (v ∈ b)),Classic.mean_hit]
  unfold graphRate; gcongr

theorem graph_step (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π) (D : Bank) (t : ℕ)
    (ht : D.size ≤ t) (clean : graphClean π D) (x : Addr) (_ : D x = none) :
    uniformMean (fun v : Words => Classic.hit (¬graphClean π (Function.update D x (some v)))) ≤ graphRate t := by
  have kl (b : Bool) : (Graph.support (masks D b)).card ≤ t := (slice_size _ (mask_inj b) capOf D).trans ht
  rcases x with ⟨b,r⟩ | z
  · have same (w : Words) := slice_same (ItsrLabel.mask b) (mask_inj b) capOf D r w
    have other (w : Words) := slice_other (ItsrLabel.mask (!b)) capOf D (ItsrLabel.mask b r) w (by intro i; cases b <;> simp [ItsrLabel.mask])
    cases b with
    | false =>
      apply cap_failure _ _ t _ (badLeft_card π hp he _ _ clean t (kl false) (kl true) r)
      intro w bad
      apply (mem_badLeft π (masks D false) (masks D true) r (capOf w)).mpr
      simp only [ItsrLabel.mask,Bool.not_false] at same other
      simpa only [graphClean,masks,same w,other w] using bad
    | true =>
      apply cap_failure _ _ t _ (badRight_card π hp he _ _ clean t (kl false) (kl true) r)
      intro w bad
      apply (mem_badRight π (masks D false) (masks D true) r (capOf w)).mpr
      simp only [ItsrLabel.mask,Bool.not_true] at same other
      simpa only [graphClean,masks,same w,other w] using bad
  · have safe (w : Words) : graphClean π (Function.update D (.inr z) (some w)) := by
      have hm (b : Bool) := slice_other (ItsrLabel.mask b) capOf D (.inr z) w (by intro i; simp [ItsrLabel.mask])
      simpa only [graphClean,masks,hm] using clean
    simp only [safe,not_true_eq_false,Classic.hit,ite_false,Classic.avg_const,zero_le]

theorem graph_budget {q : ℕ} (hq : q ≤ 3*2^100) : q * graphRate (3*2^100) ≤ ((2:ℝ≥0∞)^97)⁻¹ := by
  have c : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  unfold graphRate
  rw [c,Nat.cast_pow,Nat.cast_ofNat]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  calc
    _ ≤ ((3*2^100:ℕ):ℝ)*((extensionBudget (3*2^100):ℕ):ℝ)/2^512 := by rw [mul_div_assoc]; gcongr
    _ ≤ _ := by norm_num [extensionBudget]

end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.graph_step
#print axioms Reduction.ShakePermutation.Long.BankRun.graph_budget
