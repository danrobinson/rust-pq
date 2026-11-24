import Integration.SlhDsaCompressionSingleTarget
import MReduction.Resources

set_option exponentiation.threshold 1200
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security Resources2 ENNReal

/-- A numerical certificate for the complete at-most-one-signature bound, for messages
of at most 64 KiB and at most 2^40 quantum public compression queries. -/
theorem wide_single_benchmark :
    wideSingleBound .s192s 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^19)⁻¹ ∧
    wideSingleBound .s192f 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^22)⁻¹ ∧
    wideSingleBound .s256s 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^78)⁻¹ ∧
    wideSingleBound .s256f 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^79)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold wideSingleBound wideLossWithClasses wideProvedLoss ClassCollision.twoPhaseLoss Transcript.remainingLoss
      epsTcr SetOracle.epsPreSet SetOracle.epsUdSet MessageHash.singleLoss
    rw [MReduction.tcrTargets_192s_val]
    simp only [
      show 8*Sha2Set.s192s.vp.params.n = 192 by decide +kernel,
      show Sha2Set.s192s.vp.params.h+Sha2Set.s192s.vp.params.a*Sha2Set.s192s.vp.params.k = 301 by decide +kernel,
      show Sha2Set.s192s.vp.params.w-2 = 14 by decide +kernel,
      show SkGame.budget Sha2Set.s192s 65536 (2^40) 1 = 1101224382256 by decide +kernel,
      show forsBudget Sha2Set.s192s 65536 (2^40) 1 = 1101078005899 by decide +kernel,
      show ClassOne.budget Sha2Set.s192s 65536 (2^40) 1 = 1101227307455 by decide +kernel,
      show wotsBudget Sha2Set.s192s 65536 (2^40) 1 (wotsWinHashes Sha2Set.s192s.vp) = 1100099025446 by decide +kernel,
      show wotsBudget Sha2Set.s192s 65536 (2^40) 1 (wotsPreHashes Sha2Set.s192s.vp) = 1100099051711 by decide +kernel,
      show wotsBudget Sha2Set.s192s 65536 (2^40) 1 (wotsTcrHashes Sha2Set.s192s.vp) = 1100111238671 by decide +kernel,
      show HmacKey.budget Sha2Set.s192s 65536 (2^40) 1 = 1101224382254 by decide +kernel,
      show ClassCollision.walkMax Sha2Set.s192s = 11 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s192s 2 65536 (2^40) 1 = 1101227307458 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s192s Sha2Set.s192s.vp.params.len 65536 (2^40) 1 = 1101227307476 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s192s Sha2Set.s192s.vp.params.k 65536 (2^40) 1 = 1101227307464 by decide +kernel,
      show MessageHash.queries Sha2Set.s192s 65536 (2^40) 1 = 1101221457570 by decide +kernel]
    refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    · finiteness
    · finiteness
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  · unfold wideSingleBound wideLossWithClasses wideProvedLoss ClassCollision.twoPhaseLoss Transcript.remainingLoss
      epsTcr SetOracle.epsPreSet SetOracle.epsUdSet MessageHash.singleLoss
    rw [MReduction.tcrTargets_192f_val]
    simp only [
      show 8*Sha2Set.s192f.vp.params.n = 192 by decide +kernel,
      show Sha2Set.s192f.vp.params.h+Sha2Set.s192f.vp.params.a*Sha2Set.s192f.vp.params.k = 330 by decide +kernel,
      show Sha2Set.s192f.vp.params.w-2 = 14 by decide +kernel,
      show SkGame.budget Sha2Set.s192f 65536 (2^40) 1 = 1099607651618 by decide +kernel,
      show forsBudget Sha2Set.s192f 65536 (2^40) 1 = 1099594417728 by decide +kernel,
      show ClassOne.budget Sha2Set.s192f 65536 (2^40) 1 = 1099616517342 by decide +kernel,
      show wotsBudget Sha2Set.s192f 65536 (2^40) 1 (wotsWinHashes Sha2Set.s192f.vp) = 1099547521216 by decide +kernel,
      show wotsBudget Sha2Set.s192f 65536 (2^40) 1 (wotsPreHashes Sha2Set.s192f.vp) = 1099547547481 by decide +kernel,
      show wotsBudget Sha2Set.s192f 65536 (2^40) 1 (wotsTcrHashes Sha2Set.s192f.vp) = 1099559734441 by decide +kernel,
      show HmacKey.budget Sha2Set.s192f 65536 (2^40) 1 = 1099607651616 by decide +kernel,
      show ClassCollision.walkMax Sha2Set.s192f = 11 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s192f 2 65536 (2^40) 1 = 1099616517345 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s192f Sha2Set.s192f.vp.params.len 65536 (2^40) 1 = 1099616517363 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s192f Sha2Set.s192f.vp.params.k 65536 (2^40) 1 = 1099616517357 by decide +kernel,
      show MessageHash.queries Sha2Set.s192f 65536 (2^40) 1 = 1099598786407 by decide +kernel]
    refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    · finiteness
    · finiteness
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  · unfold wideSingleBound wideLossWithClasses wideProvedLoss ClassCollision.twoPhaseLoss Transcript.remainingLoss
      epsTcr SetOracle.epsPreSet SetOracle.epsUdSet MessageHash.singleLoss
    rw [MReduction.tcrTargets_256s_val]
    simp only [
      show 8*Sha2Set.s256s.vp.params.n = 256 by decide +kernel,
      show Sha2Set.s256s.vp.params.h+Sha2Set.s256s.vp.params.a*Sha2Set.s256s.vp.params.k = 372 by decide +kernel,
      show Sha2Set.s256s.vp.params.w-2 = 14 by decide +kernel,
      show SkGame.budget Sha2Set.s256s 65536 (2^40) 1 = 1100958588140 by decide +kernel,
      show forsBudget Sha2Set.s256s 65536 (2^40) 1 = 1100768597988 by decide +kernel,
      show ClassOne.budget Sha2Set.s256s 65536 (2^40) 1 = 1100962935769 by decide +kernel,
      show wotsBudget Sha2Set.s256s 65536 (2^40) 1 (wotsWinHashes Sha2Set.s256s.vp) = 1100267584946 by decide +kernel,
      show wotsBudget Sha2Set.s256s 65536 (2^40) 1 (wotsPreHashes Sha2Set.s256s.vp) = 1100267619451 by decide +kernel,
      show wotsBudget Sha2Set.s256s 65536 (2^40) 1 (wotsTcrHashes Sha2Set.s256s.vp) = 1100283629771 by decide +kernel,
      show HmacKey.budget Sha2Set.s256s 65536 (2^40) 1 = 1100958588138 by decide +kernel,
      show ClassCollision.walkMax Sha2Set.s256s = 19 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s256s 2 65536 (2^40) 1 = 1100962935772 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s256s Sha2Set.s256s.vp.params.len 65536 (2^40) 1 = 1100962935806 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s256s Sha2Set.s256s.vp.params.k 65536 (2^40) 1 = 1100962935782 by decide +kernel,
      show MessageHash.queries Sha2Set.s256s 65536 (2^40) 1 = 1100954241024 by decide +kernel]
    refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    · finiteness
    · finiteness
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  · unfold wideSingleBound wideLossWithClasses wideProvedLoss ClassCollision.twoPhaseLoss Transcript.remainingLoss
      epsTcr SetOracle.epsPreSet SetOracle.epsUdSet MessageHash.singleLoss
    rw [MReduction.tcrTargets_256f_val]
    simp only [
      show 8*Sha2Set.s256f.vp.params.n = 256 by decide +kernel,
      show Sha2Set.s256f.vp.params.h+Sha2Set.s256f.vp.params.a*Sha2Set.s256f.vp.params.k = 383 by decide +kernel,
      show Sha2Set.s256f.vp.params.w-2 = 14 by decide +kernel,
      show SkGame.budget Sha2Set.s256f 65536 (2^40) 1 = 1099689500240 by decide +kernel,
      show forsBudget Sha2Set.s256f 65536 (2^40) 1 = 1099671230169 by decide +kernel,
      show ClassOne.budget Sha2Set.s256f 65536 (2^40) 1 = 1099698523039 by decide +kernel,
      show wotsBudget Sha2Set.s256f 65536 (2^40) 1 (wotsWinHashes Sha2Set.s256f.vp) = 1099567669046 by decide +kernel,
      show wotsBudget Sha2Set.s256f 65536 (2^40) 1 (wotsPreHashes Sha2Set.s256f.vp) = 1099567703551 by decide +kernel,
      show wotsBudget Sha2Set.s256f 65536 (2^40) 1 (wotsTcrHashes Sha2Set.s256f.vp) = 1099583713871 by decide +kernel,
      show HmacKey.budget Sha2Set.s256f 65536 (2^40) 1 = 1099689500238 by decide +kernel,
      show ClassCollision.walkMax Sha2Set.s256f = 19 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s256f 2 65536 (2^40) 1 = 1099698523042 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s256f Sha2Set.s256f.vp.params.len 65536 (2^40) 1 = 1099698523076 by decide +kernel,
      show ClassCollision.continuationBudget Sha2Set.s256f Sha2Set.s256f.vp.params.k 65536 (2^40) 1 = 1099698523060 by decide +kernel,
      show MessageHash.queries Sha2Set.s256f 65536 (2^40) 1 = 1099680477954 by decide +kernel]
    refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    · finiteness
    · finiteness
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
end Reduction.Compression
#print axioms Reduction.Compression.wide_single_benchmark
