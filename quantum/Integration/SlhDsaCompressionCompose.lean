import Integration.SlhDsaSetEuf
import Integration.SlhDsaCompressionWotsReduction
import Integration.SlhDsaCompressionClassReduction
import Integration.SlhDsaCompressionPrfBudget

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal Resources2
open SetOracle (uniformMean)

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

local notation "B" => reduced S rand seeds F

/-- Remaining shared-table games for the four parameter sets using SHA-512 for
multi-node hashes. Message-PRF success is compared after averaging the tables. -/
noncomputable def wideRemaining : ℝ≥0∞ :=
  let msg := uniformMean (fun g => qPrfRealPr (msgPrf S.vp (randPrims (functions S g)))
    (qbPrfMsgWL sufCheck (B g)) F.ρ₀) -
    uniformMean (fun g => qPrfIdealPr (qbPrfMsgWL sufCheck (B g)) F.ρ₀)
  let itsr := uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
    (qbItsrL (B g)) F.ρ₀)
  let tcr := fun a => uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM a (B g)))
  msg + itsr + tcr 2 + tcr S.vp.params.len + tcr S.vp.params.k

/-- Explicit costs of the seven component bounds already discharged. -/
noncomputable def wideProvedLoss (L q qs : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (8*(SkGame.budget S L q qs : ℝ)^2 / 2^(8*S.vp.params.n)) +
  ENNReal.ofReal (168*(forsBudget S L q qs : ℝ)^2 / 2^(8*S.vp.params.n)) +
  3 * epsTcr S (forsBudget S L q qs) + epsTcr S (ClassOne.budget S L q qs) +
  ((S.vp.params.w - 2 : ℕ) : ℝ≥0∞) * SetOracle.epsUdSet S (wotsBudget S L q qs (wotsWinHashes S.vp)) +
  SetOracle.epsPreSet S (wotsBudget S L q qs (wotsPreHashes S.vp)) +
  epsTcr S (wotsBudget S L q qs (wotsTcrHashes S.vp))

private theorem collectLosses (key msg itsr dspr fors one two len k ud pre chain : ℝ≥0∞) :
    key + msg + itsr + (dspr + 3 * fors) + (one + two + len + k) + ud + pre + chain =
      (key + dspr + 3 * fors + one + ud + pre + chain) + (msg + itsr + two + len + k) := by
  ac_rfl

set_option maxHeartbeats 1600000 in
theorem wide_suf_partial (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideProvedLoss S c.ml q qs + wideRemaining S rand seeds F := by
  have hl := suf_ideal_compression_linear S rand seeds F
  simp only [qLinRealSufG, qLinIdealSufG, ← qLinearRealSide_eq_general, ← qLinearIdealSide_eq_general] at hl
  have h := SetOracle.composeUniform S (rand := rand) (seeds := seeds) (functions S) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one)
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one) hl
    (SkGame.real_le_ideal_budget S rand F seeds c q qs hq hs hc)
    le_add_tsub le_rfl (fors_dspr_reduction S rand seeds F c q qs hq hs hc)
    (fors_tcr_reduction S rand seeds F c q qs hq hs hc)
    (ClassOne.wide_class_tcr_reduction S rand seeds F hw c q qs hq hs hc)
    le_rfl le_rfl le_rfl
    (wide_ud_reduction S rand seeds F hw c q qs hq hs hc)
    (wide_pre_reduction S rand seeds F hw c q qs hq hs hc)
    (wide_chainTcr_reduction S rand seeds F hw c q qs hq hs hc)
  apply h.trans
  unfold wideProvedLoss wideRemaining epsTcr
  exact le_of_eq (collectLosses ..)

theorem wide_euf_partial (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      wideProvedLoss S c.ml q qs + wideRemaining S rand seeds F :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans
      (wide_suf_partial S rand seeds F hw c q qs hq hs hc)

/-- The narrow sets still require the arity-one and WOTS games because
their collection and singleton calls share the SHA-256 table. -/
noncomputable def narrowRemaining : ℝ≥0∞ :=
  let one := uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM 1 (B g)))
  let ud := uniformMean (fun g => qSM_DT_UD_RealSuccess (qrUd (B g))) -
    uniformMean (fun g => qSM_DT_UD_IdealSuccess (qrUd (B g)))
  wideRemaining S rand seeds F + one + ((S.vp.params.w - 2 : ℕ) : ℝ≥0∞) * ud +
    uniformMean (fun g => qSM_DT_PRE_Advantage (qrPre (B g))) +
    uniformMean (fun g => qSM_DT_TCR_Advantage (qrTcrT (B g)))

noncomputable def forsAndKeyLoss (L q qs : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (8*(SkGame.budget S L q qs : ℝ)^2 / 2^(8*S.vp.params.n)) +
  ENNReal.ofReal (168*(forsBudget S L q qs : ℝ)^2 / 2^(8*S.vp.params.n)) +
  3 * epsTcr S (forsBudget S L q qs)

private theorem collectForsAndKey (key msg itsr dspr fors one two len k ud pre chain : ℝ≥0∞) :
    key + msg + itsr + (dspr + 3 * fors) + (one + two + len + k) + ud + pre + chain =
      (key + dspr + 3 * fors) + ((msg + itsr + two + len + k) + one + ud + pre + chain) := by
  ac_rfl

set_option maxHeartbeats 1600000 in
/-- The address PRF and both FORS terms can be discharged for every set,
including SHA2-128s and SHA2-128f. -/
theorem suf_fors_key_partial (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      forsAndKeyLoss S c.ml q qs + narrowRemaining S rand seeds F := by
  have hl := suf_ideal_compression_linear S rand seeds F
  simp only [qLinRealSufG, qLinIdealSufG, ← qLinearRealSide_eq_general, ← qLinearIdealSide_eq_general] at hl
  have h := SetOracle.composeUniform S (rand := rand) (seeds := seeds) (functions S) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one)
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one) hl
    (SkGame.real_le_ideal_budget S rand F seeds c q qs hq hs hc)
    le_add_tsub le_rfl (fors_dspr_reduction S rand seeds F c q qs hq hs hc)
    (fors_tcr_reduction S rand seeds F c q qs hq hs hc)
    le_rfl le_rfl le_rfl le_rfl le_add_tsub le_rfl le_rfl
  exact h.trans (le_of_eq (collectForsAndKey ..))

theorem euf_fors_key_partial (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      forsAndKeyLoss S c.ml q qs + narrowRemaining S rand seeds F :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans
      (suf_fors_key_partial S rand seeds F c q qs hq hs hc)

end Reduction.Compression
#print axioms Reduction.Compression.wide_suf_partial
#print axioms Reduction.Compression.wide_euf_partial
#print axioms Reduction.Compression.suf_fors_key_partial
#print axioms Reduction.Compression.euf_fors_key_partial
