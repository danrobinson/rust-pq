import Integration.SlhDsaForsLifetime

namespace Reduction.ForsLifetime
open MLink ENNReal Num
set_option maxRecDepth 8192

/-- A common denominator for the two amplitude terms in the adaptive ITSR
bound. The signing budget is at most the full lifetime and at most 2^(2*l).
The numerator keeps the actual query count, including reduction overhead. -/
theorem digest_numerator (S : Sha2Set) (q s l : ℕ)
    (lifetime : s ≤ 2^64) (signings : s ≤ 2^(2*l)) :
    itsrBound S.vp.params q s ≤
      (((2*(2*q+1) + 2*q*2^l)^2 : ℕ) : ℝ≥0∞) / 2^(8*S.vp.params.n) := by
  let m := 4*S.vp.params.n
  let D : ℝ≥0∞ := (2:ℝ≥0∞)^m
  have width : m*2 = 8*S.vp.params.n := by dsimp [m]; omega
  have coverBits : 2*(m-1) ≤ coverageBits S := by cases S <;> decide
  have pos : 1 ≤ m := by cases S <;> decide
  have cover : ((2:ℝ≥0∞)^coverageBits S)⁻¹ ≤ (2/D)^2 := by
    rw [div_eq_mul_inv, show 2*D⁻¹ = ((2:ℝ≥0∞)^(m-1))⁻¹ by
      simpa [D] using two_pow_mul_inv 1 m pos,inv_two_pow_pow]
    exact inv_two_pow_le _ _ (by omega)
  have hs : (s : ℝ≥0∞) ≤ 2^(2*l) := by exact_mod_cast signings
  have target : (s:ℝ≥0∞)*((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ ≤ ((2:ℝ≥0∞)^l/D)^2 := by
    apply (mul_le_mul' hs le_rfl).trans_eq
    simp only [D,div_eq_mul_inv,mul_pow,inv_two_pow_pow,← pow_mul,width,Nat.mul_comm 2 l]
  apply (adaptive_digest_loss S q s lifetime).trans
  calc _ ≤ ((2*(q:ℝ≥0∞)+1)*(2/D) + 2*q*((2:ℝ≥0∞)^l/D))^2 := by
          apply pow_le_pow_left₀ zero_le _ 2
          apply add_le_add
          · apply (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl cover) (by norm_num : 0 ≤ (2⁻¹:ℝ))).trans_eq
            rw [← mul_pow,sq_rpow_half]
          · exact mul_le_mul' le_rfl ((ENNReal.rpow_le_rpow target (by norm_num : 0 ≤ (2⁻¹:ℝ))).trans_eq (sq_rpow_half _))
       _ = _ := by
          simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
          rw [← width,pow_mul]
          simp only [D,div_eq_mul_inv,ENNReal.inv_pow]
          ring
theorem fraction_certificate (n d bits : ℕ) (cert : n*d ≤ 2^bits) :
    (n:ℝ≥0∞) / 2^bits ≤ (d:ℝ≥0∞)⁻¹ := by
  by_cases zero : d = 0
  · simp [zero]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  exact_mod_cast cert

end Reduction.ForsLifetime
#print axioms Reduction.ForsLifetime.digest_numerator
