import Integration.SlhDsaComposedFinal
open ENNReal Reduction

namespace Reduction.Num

theorem one_sub_one_sub_pow_le (t : ℝ≥0∞) (ht : t ≤ 1) (γ : ℕ) :
    1 - (1 - t) ^ γ ≤ γ * t := by
  induction γ with
  | zero => simp
  | succ n ih =>
    have hu : (1 - t) ^ n ≤ 1 := pow_le_one₀ zero_le tsub_le_self
    have hne : (1 - t) ^ n ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hu
    rw [pow_succ, ENNReal.mul_sub (fun _ _ ↦ hne), mul_one]
    calc 1 - ((1 - t) ^ n - (1 - t) ^ n * t) ≤ 1 - (1 - t) ^ n + (1 - t) ^ n * t :=
          tsub_tsub_le_tsub_add
      _ ≤ n * t + 1 * t := add_le_add ih (mul_le_mul' hu le_rfl)
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * t := by push_cast; ring

/-- The cover sum of `epsItsr` is at most `2 t^k` once `s p 2^k ≤ 1/2`. -/
theorem cover_sum_le (s k : ℕ) (p t : ℝ≥0∞) (ht : t ≤ 1)
    (hr : (s : ℝ≥0∞) * p * 2 ^ k ≤ 2⁻¹) :
    ∑ γ ∈ Finset.range (s + 1),
        (s.choose γ : ℝ≥0∞) * p ^ γ * (1 - p) ^ (s - γ) * (1 - (1 - t) ^ γ) ^ k ≤
      2 * t ^ k := by
  have hterm : ∀ γ, (s.choose γ : ℝ≥0∞) * p ^ γ * (1 - p) ^ (s - γ) * (1 - (1 - t) ^ γ) ^ k ≤
      (2⁻¹) ^ γ * t ^ k := by
    intro γ
    have h1 : (s.choose γ : ℝ≥0∞) ≤ (s : ℝ≥0∞) ^ γ := by exact_mod_cast Nat.choose_le_pow s γ
    have h2 : (1 - p) ^ (s - γ) ≤ 1 := pow_le_one₀ zero_le tsub_le_self
    have h3 : (1 - (1 - t) ^ γ) ^ k ≤ ((2 : ℝ≥0∞) ^ k) ^ γ * t ^ k := by
      calc (1 - (1 - t) ^ γ) ^ k ≤ ((γ : ℝ≥0∞) * t) ^ k :=
            pow_le_pow_left₀ zero_le (one_sub_one_sub_pow_le t ht γ) k
        _ ≤ ((2 : ℝ≥0∞) ^ γ * t) ^ k := by
            gcongr
            exact_mod_cast (Nat.lt_two_pow_self).le
        _ = ((2 : ℝ≥0∞) ^ k) ^ γ * t ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm γ k]
    calc (s.choose γ : ℝ≥0∞) * p ^ γ * (1 - p) ^ (s - γ) * (1 - (1 - t) ^ γ) ^ k
        ≤ (s : ℝ≥0∞) ^ γ * p ^ γ * 1 * (((2 : ℝ≥0∞) ^ k) ^ γ * t ^ k) := by gcongr
      _ = ((s : ℝ≥0∞) * p * 2 ^ k) ^ γ * t ^ k := by rw [mul_one, mul_pow, mul_pow]; ring
      _ ≤ (2⁻¹) ^ γ * t ^ k := by gcongr
  calc _ ≤ ∑ γ ∈ Finset.range (s + 1), (2⁻¹ : ℝ≥0∞) ^ γ * t ^ k := Finset.sum_le_sum fun γ _ ↦ hterm γ
    _ = (∑ γ ∈ Finset.range (s + 1), (2⁻¹ : ℝ≥0∞) ^ γ) * t ^ k := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑' γ : ℕ, (2⁻¹ : ℝ≥0∞) ^ γ) * t ^ k := by
        gcongr
        exact ENNReal.sum_le_tsum _
    _ = 2 * t ^ k := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

end Reduction.Num
