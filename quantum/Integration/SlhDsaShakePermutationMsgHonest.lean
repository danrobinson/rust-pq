import Integration.SlhDsaShakePermutationMsgPathHybrid

namespace Reduction.ShakePermutation.MsgTrajectory
open MLink SLHDSA SLHDSA.Security Classical SetOracle ENNReal
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
variable (S : Sha2Set)

def column (k : S.Node) : SkFormat.Suffix S ↪ Words :=
  ⟨fun t => (SkFormat.split S).symm (k,t),fun _ _ eq => congrArg Prod.snd ((SkFormat.split S).symm.injective eq)⟩

def programmed (k : S.Node) (π σ : Permutation) := Risk.replacement (column S k) π σ

theorem programmed_first (k rand : S.Node) (m : List SLHDSA.Byte) (π σ : Permutation) :
    let x := join (firstBlock S k rand m) 0
    programmed S k π σ x = σ x := by
  intro x
  have first : (SkFormat.split S x).1 = k := first_key S k rand m
  let t := (SkFormat.split S x).2
  have eq : column S k t = x := by
    apply (SkFormat.split S).injective
    change SkFormat.split S ((SkFormat.split S).symm _) = _
    rw [Equiv.apply_symm_apply]; exact Prod.ext first.symm rfl
  have e := Program.reassign_hit (imageTuple (column S k) π) (imageTuple (column S k) σ) t
  change Program.reassign _ _ (π x) = σ x
  change Program.reassign _ _ (π (column S k t)) = σ (column S k t) at e
  rwa [eq] at e

private theorem loss : ((2:ℝ≥0∞)^400)⁻¹ + 483*((Fintype.card (SkFormat.Suffix S) : ℝ≥0∞)*(1/Fintype.card Words) +
    (Fintype.card (SkFormat.Suffix S) : ℝ≥0∞)*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞))) ≤ ((2:ℝ≥0∞)^116)⁻¹ := by
  have w : Fintype.card Words = 2^1600 := by
    change Fintype.card (Fin 25 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  rw [w,SkFormat.card_suffix]
  have bits : 1600-8*S.vp.params.n ≤ 1472 := by cases S <;> decide
  have lim : ((2^(1600-8*S.vp.params.n):ℕ):ℝ≥0∞) ≤ ((2^1472:ℕ):ℝ≥0∞) := Nat.cast_le.mpr (Nat.pow_le_pow_right (by decide) bits)
  apply (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add (mul_le_mul' lim le_rfl) (mul_le_mul' lim le_rfl)))).trans
  apply (ENNReal.toReal_le_toReal (by norm_num; finiteness) (by finiteness)).mp
  simp (disch := first | finiteness | positivity | (norm_num; finiteness)) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_inv,ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num

/-- Comparison *inside* the message PRF after programming the entire
secret column. The public permutation and capped encoded message may be
chosen jointly, provided the permutation satisfies the uniform path bound. -/
theorem honest_gap (π : Permutation) (good : ¬ Risk.exceptional π) (k rand : S.Node) (m : List SLHDSA.Byte)
    (cap : m.length ≤ 65536) :
    uniformMean (fun σ : Permutation =>
      if (primitives (lanes (programmed S k π σ)) S.vp.params).PRFmsg k rand m ≠
        (SkFormat.split S (suffix π (laterBlocks S rand m) (σ (join (firstBlock S k rand m) 0)))).1
      then (1:ℝ≥0∞) else 0) ≤ ((2:ℝ≥0∞)^116)⁻¹ := by
  classical
  let bs := laterBlocks S rand m
  let x := join (firstBlock S k rand m) 0
  have n : S.vp.params.n ≤ 32 := by cases S <;> decide
  have len : bs.length ≤ 483 := by simp only [bs,laterBlocks,List.length_ofFn]; omega
  have h := Risk.suffix_gap (column S k) x π bs len good
  apply le_trans _ (h.trans ((add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr len) le_rfl)).trans (loss S)))
  apply Finset.sum_le_sum
  intro σ _
  apply mul_le_mul' le_rfl
  dsimp only
  have derived := byte_prf S (programmed S k π σ) k rand m _ _ (split_blocks S k rand m)
  rw [programmed_first] at derived
  split
  · rename_i different
    have fail : suffix (Risk.replacement (column S k) π σ) bs (σ x) ≠ suffix π bs (σ x) :=
      fun eq => different (derived.trans (congrArg (fun w => (SkFormat.split S w).1) eq))
    rw [ite_eq_left fail]
  · exact zero_le

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.honest_gap
