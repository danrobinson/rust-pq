import Integration.SlhDsaShakePermutationSparseTcr

/-! Uniform certificates for one- and two-node TCR games, charging
2^100 independent classical first-phase blocks separately from quantum cost. -/
namespace Reduction.ShakePermutation.SparsePort.ArityGame
open Classical MLink SLHDSA SetOracle ENNReal
set_option exponentiation.threshold 2048
set_option maxRecDepth 8192
theorem memo_queries (S : Sha2Set) : 2^40 + 483*tcrMHashes S.vp 1 ≤ 2^41 := by cases S <;> decide +kernel

private theorem qfrac (q : ℕ) (h : q ≤ 2^41) {D : ℕ} (d : 2^128 ≤ D) :
    (2*((3*q : ℕ):ℝ≥0∞)+1)^2 / D ≤ ((2:ℝ≥0∞)^39)⁻¹ := by
  have hD : 0 < D := by omega
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_add,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one,ENNReal.toReal_inv]
  rw [← one_div,div_le_div_iff₀ (by exact_mod_cast hD) (by positivity)]
  have upper : (2*(3*(q:ℝ))+1)^2 * 2^39 ≤ 2^128 := by
    calc _ ≤ (2*(3*(2^41:ℝ))+1)^2 * 2^39 := by gcongr; exact_mod_cast h
         _ ≤ _ := by norm_num
  push_cast
  rw [one_mul]
  exact upper.trans (by exact_mod_cast d)

theorem benchmark_loss (S : Sha2Set) (ar : ℕ) (h : ar ≤ 2) (q Q : ℕ)
    (hq : q ≤ 2^41) (hQ : Q ≤ 2^100) : loss S ar q Q ≤ ((2:ℝ≥0∞)^38)⁻¹ := by
  have w : Fintype.card Words = 2^1600 := by
    change Fintype.card (Fin 25 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64,← pow_mul]
  have r : Fintype.card Rate = 2^1088 := by
    change Fintype.card (Fin 17 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64,← pow_mul]
  have d : 2^128 ≤ Fintype.card S.Node := by change _ ≤ Fintype.card (Bytes _); rw [card_bytes']; cases S <;> decide +kernel
  have j := Arity.row_bits S ar h
  unfold loss
  apply (add_le_add (add_le_add (qfrac q hq d) le_rfl) le_rfl).trans
  unfold Classic.forestPenalty; rw [w,r]
  have denom : 2^1599 ≤ 2^1600-Q := by omega
  have pen : (↑(2^1088 * (2*Q+2) : ℕ) : ℝ≥0∞)/↑(2^1600-Q : ℕ) ≤
      ↑(2^1088*(2*2^100+2) : ℕ)/↑(2^1599 : ℕ) := by
    apply ENNReal.div_le_div
    · exact_mod_cast (show 2^1088*(2*Q+2) ≤ 2^1088*(2*2^100+2) by gcongr)
    · exact_mod_cast denom
  have fake : (↑(Fintype.card (Row S ar)) : ℝ≥0∞)/↑(2^1600 : ℕ) ≤ ↑(2^768 : ℕ)/↑(2^1600 : ℕ) :=
    ENNReal.div_le_div (Nat.cast_le.mpr j) le_rfl
  have qle : (Q:ℝ≥0∞) ≤ ↑(2^100 : ℕ) := Nat.cast_le.mpr hQ
  apply (add_le_add (add_le_add le_rfl (add_le_add (mul_le_mul' qle pen) (mul_le_mul' qle fake))) le_rfl).trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add,ENNReal.toReal_div,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat]
  norm_num

end Reduction.ShakePermutation.SparsePort.ArityGame
#print axioms Reduction.ShakePermutation.SparsePort.ArityGame.benchmark_loss
