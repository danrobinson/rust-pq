import Integration.SlhDsaComposedFinal
open ENNReal Reduction

namespace Reduction.Num

theorem two_pow_mul_inv (a b : ℕ) (h : a ≤ b) :
    (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ b)⁻¹ = ((2 : ℝ≥0∞) ^ (b - a))⁻¹ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, ENNReal.mul_inv (Or.inl (by positivity))
    (Or.inl (by simp)), ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]

theorem inv_two_pow_le (a b : ℕ) (h : a ≤ b) : ((2 : ℝ≥0∞) ^ b)⁻¹ ≤ ((2 : ℝ≥0∞) ^ a)⁻¹ :=
  ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two h)

theorem inv_two_pow_pow (a k : ℕ) : (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k = ((2 : ℝ≥0∞) ^ (a * k))⁻¹ := by
  rw [ENNReal.inv_pow, ← pow_mul, ENNReal.inv_pow]

theorem sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  simpa using ENNReal.pow_rpow_inv_natCast (n := 2) two_ne_zero x

theorem inv_two_pow_eq (n : ℕ) : ((2 : ℝ≥0∞) ^ n)⁻¹ = ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

example : (2 : ℝ≥0∞) ^ 20 * ((2 : ℝ≥0∞) ^ 63)⁻¹ * 2 ^ 14 ≤ 2⁻¹ := by
  rw [mul_right_comm, ← pow_add, two_pow_mul_inv _ _ (by norm_num)]
  simpa using inv_two_pow_le 1 29 (by norm_num)

end Reduction.Num
