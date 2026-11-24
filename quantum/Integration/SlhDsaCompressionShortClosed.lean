import Integration.SlhDsaCompressionShortSignature
import Integration.SlhDsaCompressionSmallClosed
import Integration.SlhDsaCompressionSmallFloor

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)

noncomputable def smallShortClass (S : Sha2Set) (L q qs ar : ℕ) : ℝ≥0∞ :=
  if ar ≤ 2 then ShortBlocks.loss S L q qs else smallClassLoss S L q qs ar

noncomputable def smallShortBound (S : Sha2Set) (L q qs : ℕ) : ℝ≥0∞ :=
  smallWithClasses S L q qs (smallShortClass S L q qs)

variable (S : Sha2Set) (hn : S.vp.params.n = 16) (rand : S.Node → S.Node → ProbComp S.Node)
  (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
include hn

/-- The arity-one and arity-two games use the selected tweak's own random row. -/
theorem small_short_class_le (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (ar : ℕ) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g))) ≤ smallShortClass S c.ml q qs ar := by
  unfold smallShortClass
  split_ifs with ha
  · exact ShortBlocks.class_tcr_le S hn rand seeds F ar ha c q qs hq hs hc
  · exact SmallClass.class_tcr_le S hn rand seeds F ar c q qs hq hs hc

theorem small_short_suf (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ smallShortBound S c.ml q qs :=
  small_suf_with_classes S hn rand seeds F c q qs _
    (small_short_class_le S hn rand seeds F c q qs hq hs hc) hq hs hc

theorem small_short_euf (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤ smallShortBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans (small_short_suf S hn rand seeds F c q qs hq hs hc)

set_option maxRecDepth 8192 in
/-- A long class still gives a unit floor in the short-class improvement. -/
theorem small_short_floor (L q qs : ℕ) : 1 ≤ smallShortBound S L q qs := by
  have hk : ¬ S.vp.params.k ≤ 2 := by cases S <;> decide +kernel
  have h : 1 ≤ smallShortClass S L q qs S.vp.params.k := by
    rw [smallShortClass,ite_eq_right hk]
    exact small_class_floor S hn L q qs _
  unfold smallShortBound smallWithClasses smallWithComponents
  exact h.trans ((le_add_self.trans (le_self_add.trans (le_self_add.trans
    (le_self_add.trans le_self_add)))).trans le_add_self)

omit hn

set_option maxRecDepth 8192 in
/-- At one signing query, 64 KiB messages and 2^40 compression queries, each short
class contributes at most 2^-45, including its entire honest choosing phase. -/
theorem small_short_benchmark :
    ShortBlocks.loss .s128s 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^45)⁻¹ ∧
    ShortBlocks.loss .s128f 65536 (2^40) 1 ≤ ((2:ℝ≥0∞)^45)⁻¹ := by
  constructor
  · unfold ShortBlocks.loss epsTcr Wots256.phaseLoss
    rw [MReduction.tcrTargets_128s_val,show ClassOne.budget .s128s 65536 (2^40) 1 = 1101584249374 by decide +kernel]
    change _ / (2:ℝ≥0∞)^128 + _ ≤ _
    refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  · unfold ShortBlocks.loss epsTcr Wots256.phaseLoss
    rw [MReduction.tcrTargets_128f_val,show ClassOne.budget .s128f 65536 (2^40) 1 = 1099648107204 by decide +kernel]
    change _ / (2:ℝ≥0∞)^128 + _ ≤ _
    refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num

end Reduction.Compression
#print axioms Reduction.Compression.small_short_suf
#print axioms Reduction.Compression.small_short_euf
#print axioms Reduction.Compression.small_short_floor
#print axioms Reduction.Compression.small_short_benchmark
