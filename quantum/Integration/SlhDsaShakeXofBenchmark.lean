import Integration.SlhDsaShakeDigestSearch
import Integration.SlhDsaSetWots

namespace Reduction.ShakeXof
open MLink Ideal SLHDSA SLHDSA.Security ENNReal
set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

/-- Sum of the component estimates when each reduction uses at most q raw
queries. This includes two PRFs, FORS DSPR and TCR, the four tweak arities,
WOTS+ UD, PRE and TCR, and the one-target message-digest term. -/
noncomputable def singleLoss (S : Sha2Set) (q : ℕ) : ℝ≥0∞ :=
  let n := 8*S.vp.params.n
  let prf := ENNReal.ofReal (8*(q:ℝ)^2 / 2^n)
  let dspr := ENNReal.ofReal (168*(q:ℝ)^2 / 2^n)
  let tcr := (2*(q:ℝ≥0∞)+1)^2 / 2^n
  let itsr := ENNReal.ofReal (16*((q:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k))
  prf + prf + itsr + (dspr + 3*tcr) + (tcr+tcr+tcr+tcr) +
    ((S.vp.params.w-2:ℕ):ℝ≥0∞) * SetOracle.epsUdSet S q + SetOracle.epsPreSet S q + tcr

/-- Uniform numerical ceiling on the component sum with a factor-of-two
allowance above the benchmark public-query budget for internal reductions. -/
theorem singleLoss_benchmark (S : Sha2Set) :
    singleLoss S (2^41) ≤ ((2:ℝ≥0∞)^36)⁻¹ := by
  unfold singleLoss SetOracle.epsUdSet SetOracle.epsPreSet
  have digest := ShakeSingle.digest_search_budget S (q:=2^41) le_rfl
  apply le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add le_rfl digest) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
  have bits : 8*S.vp.params.n = 128 ∨ 8*S.vp.params.n = 192 ∨ 8*S.vp.params.n = 256 := by cases S <;> decide +kernel
  have w : S.vp.params.w-2 = 14 := by cases S <;> decide +kernel
  rw [w]
  rcases bits with b|b|b <;> rw [b] <;>
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp <;>
    simp (disch := first | finiteness | positivity | norm_num) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_ofReal] <;> norm_num

/-- A larger budget accommodates the coherent simulator for the public permutation. -/
theorem singleLoss_simulation (S : Sha2Set) :
    singleLoss S (2^56) ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
  unfold singleLoss SetOracle.epsUdSet SetOracle.epsPreSet
  have digest : ENNReal.ofReal (16*((2^56:ℝ)+1)^3 / 2^(S.vp.params.h+S.vp.params.a*S.vp.params.k)) ≤
      ENNReal.ofReal ((2:ℝ)^58)⁻¹ := by
    have size : 231 ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k := by cases S <;> decide +kernel
    apply ENNReal.ofReal_le_ofReal
    calc _ ≤ 16*((2^56:ℝ)+1)^3 / 2^231 := by gcongr; norm_num
         _ ≤ _ := by norm_num
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  apply le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add le_rfl digest) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
  have bits : 8*S.vp.params.n = 128 ∨ 8*S.vp.params.n = 192 ∨ 8*S.vp.params.n = 256 := by cases S <;> decide +kernel
  have w : S.vp.params.w-2 = 14 := by cases S <;> decide +kernel
  rw [w]
  rcases bits with b|b|b <;> rw [b] <;>
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp <;>
    simp (disch := first | finiteness | positivity | norm_num) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_ofReal] <;> norm_num

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.singleLoss_benchmark
#print axioms Reduction.ShakeXof.singleLoss_simulation
