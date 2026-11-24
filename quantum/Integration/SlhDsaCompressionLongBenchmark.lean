import Integration.SlhDsaCompressionSmallTotals
import Integration.SlhDsaCompressionLongSignature
namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security Resources2 ENNReal

private theorem phase_budget (t C B : ℕ) (ht : t ≤ 9) (hc : C ≤ 2^80) (hb : B ≤ 1101584249374) :
    let w := (C+C)*(1+9)
    let N := w + C*(t+1)
    let m := 2*(t+1)
    let post := ENNReal.ofReal ((2*(m:ℝ)*Real.sqrt (((2:ℝ)^256)⁻¹) +
      ((B+m:ℕ):ℝ)*(4*Real.sqrt (((2:ℝ)^128)⁻¹ + ((2*(N+((B+m)+2))+3 : ℕ):ℝ)/2^256)))^2)
    (((w*(w+1) + C*t*(C*t+2*w+1) : ℕ):ℝ≥0∞) / 2^256 +
      (((N+1:ℕ):ℝ≥0∞) / 2^256 + post)) +
      Wots256.phaseLoss (C+C) (max t 9) ≤ ((2:ℝ≥0∞)^43)⁻¹ := by
  dsimp only
  let w := (C+C)*(1+9)
  let W := ((2^80:ℕ)+(2^80))*(1+9)
  have hw : w ≤ W := by exact Nat.mul_le_mul_right _ (Nat.add_le_add hc hc)
  have hn : w + C*(t+1) ≤ W+2^80*(9+1) := by gcongr
  have hu : w*(w+1) + C*t*(C*t+2*w+1) ≤ W*(W+1)+(2^80*9)*(2^80*9+2*W+1) := by gcongr
  have hm : 2*(t+1) ≤ 20 := by omega
  have lhs := small_end_benchmark (w+C*(t+1)) (B+2*(t+1)) (2*(t+1))
    (hn.trans (by decide +kernel)) (by omega) hm
  have hu' : ((w*(w+1)+C*t*(C*t+2*w+1):ℕ):ℝ≥0∞) / 2^256 ≤
      ((W*(W+1)+(2^80*9)*(2^80*9+2*W+1):ℕ):ℝ≥0∞) / 2^256 := by gcongr
  have hn' : ((w+C*(t+1)+1:ℕ):ℝ≥0∞) / 2^256 ≤ ((W+2^80*(9+1)+1:ℕ):ℝ≥0∞)/2^256 := by gcongr
  have ch : Wots256.phaseLoss (C+C) (max t 9) ≤ Wots256.phaseLoss (2^80+2^80) 9 := by
    unfold Wots256.phaseLoss
    rw [max_eq_right ht]
    gcongr
  apply (add_le_add (add_le_add hu' (add_le_add hn' lhs)) ch).trans
  unfold Wots256.phaseLoss W
  refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num

private theorem class_cap (S : Sha2Set) (ar : ℕ) (ha : ar ≤ 35)
    (hc : tcrTargets S.vp ≤ 2^80) (hb : ClassOne.budget S 65536 (2^40) 1 ≤ 1101584249374)
    (short : ShortBlocks.loss S 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^45)⁻¹) :
    smallLongClass S 65536 (2^40) 1 ar ≤ ((2:ℝ≥0∞)^43)⁻¹ := by
  unfold smallLongClass
  split_ifs
  · refine short.trans ?_
    refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
    norm_num
  · exact phase_budget (LongPhase.tails ar) (tcrTargets S.vp) (ClassOne.budget S 65536 (2^40) 1)
      (by unfold LongPhase.tails; omega) hc hb

set_option maxRecDepth 8192 in
/-- Complete SUF and EUF loss for a 64 KiB message cap, at most one signing query,
and at most 2^40 queries to the shared ideal SHA-256/SHA-512 compression oracle. -/
theorem small_long_single_benchmark :
    smallLongSingleBound .s128s 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^39)⁻¹ ∧
    smallLongSingleBound .s128f 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^39)⁻¹ := by
  constructor
  · apply small_total_128s
    intro ar ha
    apply class_cap _ ar _ _ _ small_short_benchmark.1
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel
    · rw [MReduction.tcrTargets_128s_val]; decide +kernel
    · decide +kernel
  · apply small_total_128f
    intro ar ha
    apply class_cap _ ar _ _ _ small_short_benchmark.2
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel
    · rw [MReduction.tcrTargets_128f_val]; decide +kernel
    · decide +kernel

end Reduction.Compression
#print axioms Reduction.Compression.small_long_single_benchmark
