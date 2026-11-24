import Integration.SlhDsaShakePermutationTrajectoryRisk

namespace Reduction.ShakePermutation.MsgTrajectory.Risk
open Classical SetOracle ENNReal OracleComp OracleComp.PermutationConditioning Classic
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
variable {A : Type} [Fintype A] [DecidableEq A]

private def emptyExtensions : Extensions ([] : EdgeTrace A) ≃ Equiv.Perm A where
  toFun := Subtype.val
  invFun π := ⟨π,by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem empty_moment (g : Equiv.Perm A) (bs : List (Equiv.Perm A)) (Q n : ℕ)
    (room : n*(bs.length+1) ≤ Q) :
    uniformMean (fun π : Equiv.Perm A => (mass π g bs)^n) ≤
      ((((bs.length+2 : ℕ) : ℝ≥0∞)*penalty A Q)^n) := by
  have ok : Nonempty (Extensions ([] : EdgeTrace A)) := ⟨emptyExtensions.symm (Equiv.refl _)⟩
  have h := moments g bs Q n room [] (Nat.zero_le _) ok
  exact (Classic.mean_equiv emptyExtensions (fun π : Equiv.Perm A => (mass π g bs)^n)).symm.le.trans h

/-- A single exceptional-permutation test covers every permitted suffix,
including a suffix selected after interacting with the public permutation. -/
theorem maximal {M : Type} [Fintype M] (first : M → Equiv.Perm A) (rest : M → List (Equiv.Perm A))
    (Q n L : ℕ) (length : ∀ m, (rest m).length ≤ L) (room : n*(L+1) ≤ Q) (scale : ℝ≥0∞) :
    uniformMean (fun π : Equiv.Perm A =>
      if ∃ m, 1 ≤ scale * mass π (first m) (rest m) then (1 : ℝ≥0∞) else 0) ≤
      (Fintype.card M : ℝ≥0∞)*(scale*((L+2 : ℕ)*penalty A Q))^n := by
  classical
  let f (π : Equiv.Perm A) (m : M) := scale*mass π (first m) (rest m)
  have per (π : Equiv.Perm A) : (if ∃ m, 1 ≤ f π m then (1 : ℝ≥0∞) else 0) ≤ ∑ m, (f π m)^n := by
    split
    · rename_i ex; obtain ⟨m,h⟩ := ex
      exact (one_le_pow₀ h).trans (Finset.single_le_sum (f:=fun j => (f π j)^n) (fun _ _ => zero_le) (Finset.mem_univ m))
    · exact zero_le
  have avg (m : M) : uniformMean (fun π => (f π m)^n) ≤ (scale*((L+2 : ℕ)*penalty A Q))^n := by
    have l := length m
    have base := empty_moment (first m) (rest m) Q n ((Nat.mul_le_mul_left _ (Nat.add_le_add_right l 1)).trans room)
    simp only [f,mul_pow,uniformMean] at ⊢
    simp_rw [mul_left_comm (unifW _ _) (scale^n)]
    rw [← Finset.mul_sum]
    apply mul_le_mul' le_rfl
    apply base.trans
    rw [← mul_pow]
    gcongr
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun π _ => mul_le_mul' (le_rfl : unifW _ π ≤ _) (per π))).trans
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _m : M, (scale*((L+2 : ℕ)*penalty A Q))^n := Finset.sum_le_sum fun m _ => avg m
       _ = _ := by simp [nsmul_eq_mul]

abbrev Blocks := Fin 483 → Rate
def next (v : Blocks) : List Permutation :=
  List.ofFn (fun i : Fin 482 => absorbBlock (v i.succ))

def exceptional (π : Permutation) : Prop :=
  ∃ v : Blocks, 1 ≤ (2:ℝ≥0∞)^400 * mass π (absorbBlock (v 0)) (next v)

private theorem words_card : Fintype.card Words = 2^1600 := by
  change Fintype.card (Fin 25 → UInt64) = _
  rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
  decide +kernel

private theorem blocks_card : Fintype.card Blocks = 2^(1088*483) := by
  have r : Fintype.card Rate = 2^1088 := by
    change Fintype.card (Fin 17 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  change Fintype.card (Fin 483 → Rate) = _
  rw [Fintype.card_fun,Fintype.card_fin,r,pow_mul]

private theorem exponents (a b n c : ℕ) (h : a+c ≤ b*n) :
    (2:ℝ≥0∞)^a * (((2:ℝ≥0∞)^b)⁻¹)^n ≤ ((2:ℝ≥0∞)^c)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat,inv_pow,← pow_mul]
  have le : (2:ℝ)^(a+c) ≤ 2^(b*n) := pow_le_pow_right₀ (by norm_num) h
  have pos : (0:ℝ) < 2^(a+c) := by positivity
  apply (mul_le_mul_of_nonneg_left (inv_anti₀ pos le) (by positivity : (0:ℝ) ≤ 2^a)).trans
  rw [pow_add,mul_inv_rev]
  field_simp; rfl

/-- Simultaneously for all possible lists of 483 rate blocks, a random
permutation almost surely has at most a 2^-400 fraction of starting states
that return to themselves during that path. -/
theorem exceptional_risk :
    uniformMean (fun π : Permutation => if exceptional π then (1:ℝ≥0∞) else 0) ≤ ((2:ℝ≥0∞)^512)⁻¹ := by
  classical
  have h := maximal (fun v : Blocks => absorbBlock (v 0)) next (2^20) 1024 482
    (fun v => by simp only [next,List.length_ofFn,le_refl]) (by decide) ((2:ℝ≥0∞)^400)
  let Y : Permutation → ℝ≥0∞ := fun π =>
    if ∃ v : Blocks, 1 ≤ (2:ℝ≥0∞)^400*mass π (absorbBlock (v 0)) (next v) then 1 else 0
  have eq : (fun π => if exceptional π then (1:ℝ≥0∞) else 0) = Y := by
    funext π
    by_cases e : exceptional π
    · rw [ite_eq_left e]; exact (ite_eq_left (c:=∃ v : Blocks, 1 ≤ (2:ℝ≥0∞)^400*mass π (absorbBlock (v 0)) (next v)) e).symm
    · rw [ite_eq_right e]; exact (ite_eq_right (c:=∃ v : Blocks, 1 ≤ (2:ℝ≥0∞)^400*mass π (absorbBlock (v 0)) (next v)) e).symm
  rw [eq]
  change uniformMean Y ≤ _ at h
  apply le_trans h
  have factor : (2:ℝ≥0∞)^400 * (↑(482+2 : ℕ)*penalty Words (2^20)) ≤ ((2:ℝ≥0∞)^1160)⁻¹ := by
    unfold penalty; rw [words_card]
    apply (ENNReal.toReal_le_toReal (by norm_num; finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_div,
      ENNReal.toReal_inv,ENNReal.toReal_ofNat]
    norm_num
  rw [blocks_card,Nat.cast_pow,Nat.cast_ofNat]
  apply (mul_le_mul' le_rfl (pow_le_pow_left' factor 1024)).trans
  exact exponents (1088*483) 1160 1024 512 (by decide)

end
end Reduction.ShakePermutation.MsgTrajectory.Risk
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.maximal
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.exceptional_risk
