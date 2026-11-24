import Integration.SlhDsaCompressionTargetSubset
import MReduction.Resources
namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security Resources2 ENNReal

/-- All the numerical terms in the shared-compression bound have nonnegative
integer numerators and positive dyadic denominators. Evaluate those ratios
in the rationals so the kernel can replay concrete benchmark inequalities. -/
private def quotientBound (S : Sha2Set) (L q qs d targets : ℕ) : ℚ :=
  let n := 8*S.vp.params.n
  let square := fun x : ℕ => (2*x+1)^2
  let cube := fun x : ℕ => 16*(x+1)^3
  let dyadic := fun x bits : ℕ => (x:ℚ)/2^bits
  let sk := SkGame.budget S L q qs
  let f := forsBudget S L q qs
  let wo := fun post => wotsBudget S L q qs post
  let key := HmacKey.budget S L q qs
  let count := targets*ClassCollision.walkMax S
  let phase := fun ar =>
    let c := ClassCollision.continuationBudget S ar L q qs
    dyadic (count^2) n + (dyadic (cube c) n + dyadic (square c * count) n)
  let itsr := MessageHash.queries S L q qs
  dyadic (8*sk^2) n + dyadic (168*f^2) n + 3*dyadic (square f) n +
    dyadic (square (ClassOne.budget S L q qs)) n +
    ↑(S.vp.params.w-2)*dyadic (8*(wo (wotsWinHashes S.vp))^2) n +
    2*dyadic (square (wo (wotsPreHashes S.vp))) n +
    dyadic (square (wo (wotsTcrHashes S.vp))) n +
    (dyadic (square (key+(key+key))) 512 + dyadic (cube (key+(key+key))) n +
    dyadic (8*key^2) 512 + dyadic (8*key^2) n) +
    phase 2 + phase S.vp.params.len + phase S.vp.params.k +
    ↑(S.vp.params.k.choose (d+1)) *
      (dyadic (square itsr) 512 + dyadic (cube itsr) (S.vp.params.h+S.vp.params.a*(d+1)))

set_option exponentiation.threshold 1200 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem certificate (S : Sha2Set) (L q qs d bits : ℕ)
    (h : quotientBound S L q qs d (tcrTargets S.vp) ≤ (2^bits:ℚ)⁻¹) :
    wideMaskBound S L q qs d ≤ ((2:ℝ≥0∞)^bits)⁻¹ := by
  unfold wideMaskBound wideLossWithClasses wideProvedLoss ClassCollision.twoPhaseLoss Transcript.remainingLoss
    epsTcr SetOracle.epsPreSet SetOracle.epsUdSet MessageHash.maskLoss
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · finiteness
  · finiteness
  have realh := (Rat.cast_le (K := ℝ)).mpr h
  unfold quotientBound at realh
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_add, Nat.cast_pow, Nat.cast_mul] 
  push_cast at realh
  convert realh using 1
  ring


/-- Complete shared-compression bound at 2 signatures, 64 KiB, and 2^40 public queries. -/
theorem wide_two_benchmark :
    wideMaskBound .s192s 65536 (2^40) 2 8 ≤ ((2:ℝ≥0∞)^19)⁻¹ ∧
    wideMaskBound .s192f 65536 (2^40) 2 16 ≤ ((2:ℝ≥0∞)^22)⁻¹ ∧
    wideMaskBound .s256s 65536 (2^40) 2 10 ≤ ((2:ℝ≥0∞)^74)⁻¹ ∧
    wideMaskBound .s256f 65536 (2^40) 2 17 ≤ ((2:ℝ≥0∞)^73)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply certificate
  · rw [MReduction.tcrTargets_192s_val]; decide +kernel
  · rw [MReduction.tcrTargets_192f_val]; decide +kernel
  · rw [MReduction.tcrTargets_256s_val]; decide +kernel
  · rw [MReduction.tcrTargets_256f_val]; decide +kernel

/-- Complete shared-compression bound at 3 signatures, 64 KiB, and 2^40 public queries. -/
theorem wide_three_benchmark :
    wideMaskBound .s192s 65536 (2^40) 3 5 ≤ ((2:ℝ≥0∞)^9)⁻¹ ∧
    wideMaskBound .s192f 65536 (2^40) 3 10 ≤ ((2:ℝ≥0∞)^2)⁻¹ ∧
    wideMaskBound .s256s 65536 (2^40) 3 7 ≤ ((2:ℝ≥0∞)^33)⁻¹ ∧
    wideMaskBound .s256f 65536 (2^40) 3 11 ≤ ((2:ℝ≥0∞)^22)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply certificate
  · rw [MReduction.tcrTargets_192s_val]; decide +kernel
  · rw [MReduction.tcrTargets_192f_val]; decide +kernel
  · rw [MReduction.tcrTargets_256s_val]; decide +kernel
  · rw [MReduction.tcrTargets_256f_val]; decide +kernel

/-- Complete shared-compression bound at 4 signatures, 64 KiB, and 2^40 public queries. -/
theorem wide_four_benchmark :
    wideMaskBound .s256s 65536 (2^40) 4 5 ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
  apply certificate
  rw [MReduction.tcrTargets_256s_val]
  decide +kernel

end Reduction.Compression
#print axioms Reduction.Compression.wide_two_benchmark
#print axioms Reduction.Compression.wide_three_benchmark
#print axioms Reduction.Compression.wide_four_benchmark
