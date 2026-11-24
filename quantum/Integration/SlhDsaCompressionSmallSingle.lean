import Integration.SlhDsaCompressionSmallSingleTarget
import Integration.SlhDsaCompressionShortClosed

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal

noncomputable def smallSingleBound (S : Sha2Set) (L q qs : ℕ) :=
  smallWithComponents S L q qs (SmallItsr.loss S L q qs (S.vp.params.a * S.vp.params.k)) (smallShortClass S L q qs)

variable (S : Sha2Set) (hn : S.vp.params.n = 16) (rand : S.Node → S.Node → ProbComp S.Node)
  (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
variable (c : Caps) (q qs : ℕ) (single : qs ≤ 1) (hq : ∀ pk, CountBound isPort (F.main pk) q)
  (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
include hn single hq hs hc

theorem small_single_suf :
    SetOracle.uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      smallSingleBound S c.ml q qs :=
  small_suf_with_components S hn rand seeds F c q qs _ _
    (SmallItsr.single_itsr S hn rand seeds F c q qs single hq hs hc)
    (small_short_class_le S hn rand seeds F c q qs hq hs hc) hq hs hc

theorem small_single_euf :
    SetOracle.uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      smallSingleBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans
    (small_single_suf S hn rand seeds F c q qs single hq hs hc)

omit hn single hq hs hc in
/-- The message-hash component of the single-signature shared-compression bound
at up to 64 KiB and 2^40 public queries. -/
theorem small_single_itsr_benchmark :
    SmallItsr.loss .s128s 65536 (2^40) 1 (Sha2Set.s128s.vp.params.a * Sha2Set.s128s.vp.params.k) ≤ ((2:ℝ≥0∞)^43)⁻¹ ∧
    SmallItsr.loss .s128f 65536 (2^40) 1 (Sha2Set.s128f.vp.params.a * Sha2Set.s128f.vp.params.k) ≤ ((2:ℝ≥0∞)^73)⁻¹ := by
  constructor
  · unfold SmallItsr.loss
    rw [show SmallItsr.budget .s128s 65536 (2^40) 1 = 1101576184347 by decide +kernel]
    change _ + _ / (2:ℝ≥0∞)^168 ≤ _
    refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  · unfold SmallItsr.loss
    rw [show SmallItsr.budget .s128f 65536 (2^40) 1 = 1099623681827 by decide +kernel]
    change _ + _ / (2:ℝ≥0∞)^198 ≤ _
    refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
end Reduction.Compression
#print axioms Reduction.Compression.small_single_suf
#print axioms Reduction.Compression.small_single_euf
#print axioms Reduction.Compression.small_single_itsr_benchmark
