import Integration.SlhDsaCompressionSmallSingle
import MReduction.Resources

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security Resources2 ENNReal

set_option exponentiation.threshold 1200
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- Full narrow-set composition at the benchmark budgets, given a uniform
upper bound on the four arity-specific TCR contributions. -/
theorem small_total_128s (ar : ℕ → ℝ≥0∞)
    (h : ∀ a ∈ [2,Sha2Set.s128s.vp.params.len,Sha2Set.s128s.vp.params.k,1], ar a ≤ ((2:ℝ≥0∞)^43)⁻¹) :
    smallWithComponents .s128s 65536 (2^40) 1
      (SmallItsr.loss .s128s 65536 (2^40) 1 (Sha2Set.s128s.vp.params.a*Sha2Set.s128s.vp.params.k)) ar ≤ ((2:ℝ≥0∞)^39)⁻¹ := by
  have hi := small_single_itsr_benchmark.1
  unfold smallWithComponents
  apply le_trans (add_le_add le_rfl (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hi) (h 2 (by simp)))
    (h _ (by simp))) (h _ (by simp))) (h 1 (by simp))) le_rfl) le_rfl) le_rfl))
  unfold forsAndKeyLoss Hmac256.loss Wots256.phaseLoss epsTcr SetOracle.epsUdSet SetOracle.epsPreSet
  simp only [Wots256.chooseBudget_128s,
    show Sha2Set.s128s.vp.params.w-2 = 14 by decide +kernel,
    show 8*Sha2Set.s128s.vp.params.n = 128 by decide +kernel,
    show SkGame.budget .s128s 65536 (2^40) 1 = 1101580216346 by decide +kernel,
    show forsBudget .s128s 65536 (2^40) 1 = 1101517275651 by decide +kernel,
    show HmacKey.budget .s128s 65536 (2^40) 1 = 1101580215832 by decide +kernel,
    show wotsBudget .s128s 65536 (2^40) 1 (wotsWinHashes Sha2Set.s128s.vp) = 1099770530368 by decide +kernel,
    show wotsBudget .s128s 65536 (2^40) 1 (wotsPreHashes Sha2Set.s128s.vp) = 1099770566313 by decide +kernel,
    show wotsBudget .s128s 65536 (2^40) 1 (wotsTcrHashes Sha2Set.s128s.vp) = 1099787244793 by decide +kernel]
  refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    ENNReal.toReal_one]
  norm_num
/-- Full narrow-set composition at the benchmark budgets, given a uniform
upper bound on the four arity-specific TCR contributions. -/
theorem small_total_128f (ar : ℕ → ℝ≥0∞)
    (h : ∀ a ∈ [2,Sha2Set.s128f.vp.params.len,Sha2Set.s128f.vp.params.k,1], ar a ≤ ((2:ℝ≥0∞)^43)⁻¹) :
    smallWithComponents .s128f 65536 (2^40) 1
      (SmallItsr.loss .s128f 65536 (2^40) 1 (Sha2Set.s128f.vp.params.a*Sha2Set.s128f.vp.params.k)) ar ≤ ((2:ℝ≥0∞)^39)⁻¹ := by
  have hi := small_single_itsr_benchmark.2
  unfold smallWithComponents
  apply le_trans (add_le_add le_rfl (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hi) (h 2 (by simp)))
    (h _ (by simp))) (h _ (by simp))) (h 1 (by simp))) le_rfl) le_rfl) le_rfl))
  unfold forsAndKeyLoss Hmac256.loss Wots256.phaseLoss epsTcr SetOracle.epsUdSet SetOracle.epsPreSet
  simp only [Wots256.chooseBudget_128f,
    show Sha2Set.s128f.vp.params.w-2 = 14 by decide +kernel,
    show 8*Sha2Set.s128f.vp.params.n = 128 by decide +kernel,
    show SkGame.budget .s128f 65536 (2^40) 1 = 1099635894002 by decide +kernel,
    show forsBudget .s128f 65536 (2^40) 1 = 1099621472634 by decide +kernel,
    show HmacKey.budget .s128f 65536 (2^40) 1 = 1099635893488 by decide +kernel,
    show wotsBudget .s128f 65536 (2^40) 1 (wotsWinHashes Sha2Set.s128f.vp) = 1099546016956 by decide +kernel,
    show wotsBudget .s128f 65536 (2^40) 1 (wotsPreHashes Sha2Set.s128f.vp) = 1099546052971 by decide +kernel,
    show wotsBudget .s128f 65536 (2^40) 1 (wotsTcrHashes Sha2Set.s128f.vp) = 1099562763931 by decide +kernel]
  refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    ENNReal.toReal_one]
  norm_num

/-- A rational envelope for the square roots arising in the fixed-cache verifier.
The range covers both narrow parameter sets and both long arities at the benchmark. -/
theorem small_end_benchmark (N Q m : ℕ) (hN : N ≤ 2^90) (hQ : Q ≤ 17*2^36) (hm : m ≤ 20) :
    ENNReal.ofReal ((2*(m:ℝ)*Real.sqrt (((2:ℝ)^256)⁻¹) +
      (Q:ℝ)*(4*Real.sqrt (((2:ℝ)^128)⁻¹ + ((2*(N+(Q+2))+3 : ℕ):ℝ)/2^256)))^2) ≤ 25/(2:ℝ≥0∞)^48 := by
  have hn : (N:ℝ) ≤ 2^90 := by exact_mod_cast hN
  have hq : (Q:ℝ) ≤ 17*2^36 := by exact_mod_cast hQ
  have hm' : (m:ℝ) ≤ 20 := by exact_mod_cast hm
  have small : Real.sqrt (((2:ℝ)^256)⁻¹) ≤ ((2:ℝ)^64)⁻¹ := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    norm_num
  have big : Real.sqrt (((2:ℝ)^128)⁻¹ + ((2*(N+(Q+2))+3 : ℕ):ℝ)/2^256) ≤ 17/16*((2:ℝ)^64)⁻¹ := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast
    norm_num only [Nat.cast_ofNat] at hn hq
    norm_num
    linarith
  have amp := add_le_add
    (mul_le_mul (mul_le_mul_of_nonneg_left hm' (by positivity : 0 ≤ (2:ℝ))) small (Real.sqrt_nonneg _) (by positivity))
    (mul_le_mul hq (mul_le_mul_of_nonneg_left big (by positivity : 0 ≤ (4:ℝ))) (by positivity) (by positivity))
  have ampl := amp.trans (by norm_num : (2*(20:ℝ)*((2:ℝ)^64)⁻¹ + 17*2^36*(4*(17/16*((2:ℝ)^64)⁻¹))) ≤ 5/2^24)
  refine (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).mp ?_
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  apply ((sq_le_sq₀ (by positivity) (by positivity)).mpr ampl).trans
  norm_num

end Reduction.Compression
#print axioms Reduction.Compression.small_total_128s
#print axioms Reduction.Compression.small_total_128f

#print axioms Reduction.Compression.small_end_benchmark
