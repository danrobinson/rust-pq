import Integration.SlhDsaShakePermutationItsrRecorded

namespace Reduction.ShakePermutation.ItsrLabel
open MLink Quantum ENNReal
set_option exponentiation.threshold 2048
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000
private theorem lanes_count (n : ℕ) : Fintype.card (Fin n → UInt64) = (2^64)^n := by
  rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]

theorem price_small (S : Sha2Set) {q m : ℕ} (hq : q ≤ 2^46) (hm : m ≤ 2^12) :
    price S q m ≤ ((2:ℝ)^82)⁻¹ := by
  have c : Fintype.card Capacity = 2^512 := (lanes_count 8).trans (by rfl)
  have w : Fintype.card Words = 2^1600 := (lanes_count 25).trans (by rfl)
  have hbits : 231 ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k := by cases S <;> decide +kernel
  have lower : (2:ℝ)^231 ≤ 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) := pow_le_pow_right₀ (by norm_num) hbits
  have t : q+1 ≤ 2^47 := by omega
  have hcap : extensionBudget (q+1)+(q+1) ≤ extensionBudget (2^47)+(2^47) := by
    unfold extensionBudget; gcongr
  have den : (Fintype.card Capacity : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have r : (rateBound S (q+1)).toReal ≤ (((2:ℝ)^90)⁻¹)^2 := by
    rw [rateBound,ENNReal.toReal_add (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) den)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num)))]
    simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat,c,Nat.cast_pow,Nat.cast_ofNat]
    calc
      _ ≤ ((extensionBudget (2^47)+2^47:ℕ):ℝ)/2^512 + ((2^47:ℕ):ℝ)/2^231 := by gcongr
      _ ≤ _ := by norm_num [extensionBudget]
  have dr := Real.sqrt_le_sqrt r
  rw [Real.sqrt_sq (by positivity : 0 ≤ ((2:ℝ)^90)⁻¹)] at dr
  have dw : Real.sqrt (Fintype.card Words : ℝ)⁻¹ ≤ ((2:ℝ)^800)⁻¹ := by
    rw [Real.sqrt_le_left (by positivity),w,Nat.cast_pow,Nat.cast_ofNat]
    norm_num
  unfold price
  calc
    _ ≤ (2*((2^12:ℕ):ℝ)*((2:ℝ)^800)⁻¹ + ((2^46:ℕ):ℝ)*(4*((2:ℝ)^90)⁻¹))^2 := by gcongr
    _ ≤ _ := by norm_num

end Reduction.ShakePermutation.ItsrLabel
#print axioms Reduction.ShakePermutation.ItsrLabel.price_small
