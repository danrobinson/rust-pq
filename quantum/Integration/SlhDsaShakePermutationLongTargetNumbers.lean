import Integration.SlhDsaShakePermutationLongTargetGrowth

namespace Reduction.ShakePermutation.ItsrLabel.Target
open MLink Quantum ENNReal
set_option exponentiation.threshold 2048
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
private theorem lanes_count (n : ℕ) : Fintype.card (Fin n → UInt64) = (2^64)^n := by
  rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]

theorem rate_finite (S : Sha2Set) (t : ℕ) : rateBound S t ≠ ⊤ := by
  unfold rateBound
  have c : (Fintype.card Capacity : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have n : (Fintype.card S.Node : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) c,ENNReal.inv_ne_top.mpr n⟩

/-- All six sets, including a classical selection phase with up to 2^104
already recorded private words. -/
theorem price_small (S : Sha2Set) {p q m : ℕ} (hp : p ≤ 2^104) (hq : q ≤ 2^46) (hm : m ≤ 2^12) :
    (2*(m:ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹ + q*(4*Real.sqrt (rateBound S (p+(q+1))).toReal))^2 ≤ ((2:ℝ)^28)⁻¹ := by
  have c : Fintype.card Capacity = 2^512 := (lanes_count 8).trans (by rfl)
  have w : Fintype.card Words = 2^1600 := (lanes_count 25).trans (by rfl)
  have hbits : 2^128 ≤ Fintype.card S.Node := by
    change _ ≤ Fintype.card (SLHDSA.Bytes _)
    rw [card_bytes']; cases S <;> decide +kernel
  have lower : (2:ℝ)^128 ≤ Fintype.card S.Node := by exact_mod_cast hbits
  have t : p+(q+1) ≤ 2^105 := by omega
  have hcap : extensionBudget (p+(q+1))+(p+(q+1)) ≤ extensionBudget (2^105)+2^105 := by
    unfold extensionBudget; gcongr
  have hc : (Fintype.card Capacity : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card S.Node : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have r : (rateBound S (p+(q+1))).toReal ≤ (((2:ℝ)^63)⁻¹)^2 := by
    rw [rateBound,ENNReal.toReal_add (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc) (ENNReal.inv_ne_top.mpr hn)]
    simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,c,Nat.cast_pow,Nat.cast_ofNat]
    calc
      _ ≤ ((extensionBudget (2^105)+2^105:ℕ):ℝ)/2^512 + ((2:ℝ)^128)⁻¹ := by gcongr
      _ ≤ _ := by norm_num [extensionBudget]
  have dr := Real.sqrt_le_sqrt r
  rw [Real.sqrt_sq (by positivity : 0 ≤ ((2:ℝ)^63)⁻¹)] at dr
  have dw : Real.sqrt (Fintype.card Words : ℝ)⁻¹ ≤ ((2:ℝ)^800)⁻¹ := by
    rw [Real.sqrt_le_left (by positivity),w,Nat.cast_pow,Nat.cast_ofNat]
    norm_num
  calc
    _ ≤ (2*((2^12:ℕ):ℝ)*((2:ℝ)^800)⁻¹ + ((2^46:ℕ):ℝ)*(4*((2:ℝ)^63)⁻¹))^2 := by gcongr
    _ ≤ _ := by norm_num

end Reduction.ShakePermutation.ItsrLabel.Target
#print axioms Reduction.ShakePermutation.ItsrLabel.Target.price_small
