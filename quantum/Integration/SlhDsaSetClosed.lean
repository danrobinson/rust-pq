import Integration.SlhDsaSetItsr
import Integration.SlhDsaSetWots
import Integration.SlhDsaSetMsgPrf

namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive Quantum
variable (S : Sha2Set)
noncomputable def uniformMean {Ω : Type} [Fintype Ω] (f : Ω → ℝ≥0∞) := ∑ ω, unifW _ ω * f ω

private lemma mean_add {Ω : Type} [Fintype Ω] (f g : Ω → ℝ≥0∞) :
    uniformMean (fun ω => f ω + g ω) = uniformMean f + uniformMean g := by
  simp only [uniformMean, mul_add, Finset.sum_add_distrib]

private lemma mean_const_mul {Ω : Type} [Fintype Ω] (a : ℝ≥0∞) (f : Ω → ℝ≥0∞) :
    uniformMean (fun ω => a * f ω) = a * uniformMean f := by
  simp only [uniformMean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

private lemma mean_ne_top {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ≥0∞)
    (hf : ∀ ω, f ω ≠ ⊤) : uniformMean f ≠ ⊤ := by
  refine ENNReal.sum_ne_top.2 fun ω _ ↦ ENNReal.mul_ne_top ?_ (hf ω)
  exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

lemma avg_const_mul (c : Caps) (a : ℝ≥0∞) (f : FinFns S.vp.params c → ℝ≥0∞) :
    avg S c (fun ω => a * f ω) = a * avg S c f := mean_const_mul a f

lemma avg_ne_top (c : Caps) (f : FinFns S.vp.params c → ℝ≥0∞) (hf : ∀ ω, f ω ≠ ⊤) :
    avg S c f ≠ ⊤ := mean_ne_top f hf

variable {rand : S.Node → S.Node → ProbComp S.Node} {seeds : ProbComp S.Node} {W : Type} [Fintype W]

/-- Compose averaged hash games for any finite distribution obtained by uniform
sampling of a world. The functions within each world may share tables. -/
theorem composeFamily (vp : ValidatedParams) {Ω : Type} [Fintype Ω] [Nonempty Ω] (P : Ω → Primitives vp.params)
    [∀ ω, SampleableType (P ω).SkSeed] [∀ ω, SampleableType (P ω).SkPrf] [∀ ω, SampleableType (P ω).Y]
    [∀ ω, DecidableEq (P ω).Y] [∀ ω, DecidableEq (P ω).PkSeed] [∀ ω, DecidableEq (P ω).AdrsKey]
    [∀ ω, Inhabited (P ω).Y] [∀ ω, Fintype (P ω).Y]
    {coins : ∀ ω, PublicKeyCore (P ω).core → ProbComp (P ω).Y} {keys : ∀ ω, ProbComp (P ω).PkSeed}
    (B : ∀ ω, QForger W (internalAlg vp (P ω) (coins ω) (keys ω)))
    (adv R₁ I₁ R₂ I₂ : Ω → ℝ≥0∞)
    (ePrf eMsg eItsr eDspr eFv e1 e2 eLen eK eUd ePre eT : ℝ≥0∞)
    (hI₁ : ∀ ω, I₁ ω ≤ 1) (hI₂ : ∀ ω, I₂ ω ≤ 1)
    (hlin : uniformMean adv + uniformMean (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≤
      uniformMean (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)))
    (hprf : uniformMean R₁ ≤ uniformMean I₁ + ePrf) (hmsg : uniformMean R₂ ≤ uniformMean I₂ + eMsg)
    (hitsr : uniformMean (fun ω ↦
      qItsrAdvantage (itsrProblem vp (P ω)) (qbItsrL (B ω)) (B ω).ρ₀) ≤ eItsr)
    (hdspr : uniformMean (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) ≤
      uniformMean (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + eDspr)
    (hfv : uniformMean (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ eFv)
    (h1 : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) ≤ e1)
    (h2 : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) ≤ e2)
    (hLen : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM vp.params.len (B ω))) ≤ eLen)
    (hK : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM vp.params.k (B ω))) ≤ eK)
    (hud : uniformMean (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
      uniformMean (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd)
    (hpre : uniformMean (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) ≤ ePre)
    (hT : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) ≤ eT) :
    uniformMean adv ≤ ePrf + eMsg + eItsr + (eDspr + 3 * eFv) + (e1 + e2 + eLen + eK) +
      ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * eUd + ePre + eT := by
  have hfin : uniformMean (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≠ ⊤ := by
    refine mean_ne_top _ fun ω ↦ ?_
    have h1 := hI₁ ω
    have h2 := hI₂ ω
    have h3 : qDsprFV_SPProbability (qToDspr (B ω)) ≤ 1 :=
      qWeight_le_one _ _ (qToDspr (B ω)).posSemidef (qToDspr (B ω)).trace_eq_one
    have h4 : qSM_DT_UD_IdealSuccess (qrUd (B ω)) ≤ 1 :=
      qWeight_le_one _ _ (qrUd (B ω)).posSemidef (qrUd (B ω)).trace_eq_one
    unfold qLinearIdealSide
    refine ne_top_of_le_ne_top (b := 1 + 1 + 1 + ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1) ?_ ?_
    · simp
    · gcongr
  have hId : uniformMean (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) =
      uniformMean I₁ + uniformMean I₂ + uniformMean (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          uniformMean (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) := by
    unfold qLinearIdealSide
    simp only [mean_add, mean_const_mul]
  have hRe : uniformMean (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)) =
      uniformMean R₁ + uniformMean R₂ +
        uniformMean (fun ω ↦ qItsrAdvantage (itsrProblem vp (P ω)) (qbItsrL (B ω)) (B ω).ρ₀) +
        (uniformMean (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) +
          3 * uniformMean (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω)))) +
        (uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) +
          uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) +
          uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM vp.params.len (B ω))) +
          uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM vp.params.k (B ω)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          uniformMean (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) +
        uniformMean (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) +
        uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) := by
    unfold qLinearRealSide
    simp only [mean_add, mean_const_mul]
  have hle : uniformMean (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)) ≤
      (ePrf + eMsg + eItsr + (eDspr + 3 * eFv) + (e1 + e2 + eLen + eK) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * eUd + ePre + eT) +
        uniformMean (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) := by
    rw [hRe, hId]
    have hud' : ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          uniformMean (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          (uniformMean (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd) := by
      gcongr
    have hfv' : 3 * uniformMean (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ 3 * eFv := by
      gcongr
    calc _ ≤ (uniformMean I₁ + ePrf) + (uniformMean I₂ + eMsg) + eItsr +
          ((uniformMean (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + eDspr) + 3 * eFv) +
          (e1 + e2 + eLen + eK) +
          ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
            (uniformMean (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd) +
          ePre + eT :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add hprf hmsg) hitsr) (add_le_add hdspr hfv'))
          (add_le_add (add_le_add (add_le_add h1 h2) hLen) hK)) hud') hpre) hT
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 (hlin.trans hle)


theorem composeUniform {Ω : Type} [Fintype Ω] [Nonempty Ω] (world : Ω → RandFns S.vp.params)
    (B : ∀ ω, QForger W (internalAlg S.vp (randPrims (world ω)) (fun pk => rand pk.pkSeed pk.pkRoot) seeds))
    (adv R₁ I₁ R₂ I₂ : Ω → ℝ≥0∞)
    (ePrf eMsg eItsr eDspr eFv e1 e2 eLen eK eUd ePre eT : ℝ≥0∞)
    (hI₁ : ∀ ω, I₁ ω ≤ 1) (hI₂ : ∀ ω, I₂ ω ≤ 1)
    (hlin : uniformMean adv + uniformMean (fun ω ↦ qLinearIdealSide (B ω) (I₁ ω) (I₂ ω)) ≤
      uniformMean (fun ω ↦ qLinearRealSide (B ω) (R₁ ω) (R₂ ω)))
    (hprf : uniformMean R₁ ≤ uniformMean I₁ + ePrf) (hmsg : uniformMean R₂ ≤ uniformMean I₂ + eMsg)
    (hitsr : uniformMean (fun ω ↦
      qItsrAdvantage (itsrProblem S.vp (randPrims (world ω))) (qbItsrL (B ω)) (B ω).ρ₀) ≤ eItsr)
    (hdspr : uniformMean (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) ≤
      uniformMean (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + eDspr)
    (hfv : uniformMean (fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) ≤ eFv)
    (h1 : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) ≤ e1)
    (h2 : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) ≤ e2)
    (hLen : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM S.vp.params.len (B ω))) ≤ eLen)
    (hK : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM S.vp.params.k (B ω))) ≤ eK)
    (hud : uniformMean (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω))) ≤
      uniformMean (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) + eUd)
    (hpre : uniformMean (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) ≤ ePre)
    (hT : uniformMean (fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) ≤ eT) :
    uniformMean adv ≤ ePrf + eMsg + eItsr + (eDspr + 3 * eFv) + (e1 + e2 + eLen + eK) +
      ((S.vp.params.w - 2 : ℕ) : ℝ≥0∞) * eUd + ePre + eT :=
  composeFamily S.vp (fun ω => randPrims (world ω)) B adv R₁ I₁ R₂ I₂
    ePrf eMsg eItsr eDspr eFv e1 e2 eLen eK eUd ePre eT hI₁ hI₂ hlin
    hprf hmsg hitsr hdspr hfv h1 h2 hLen hK hud hpre hT

/-- Forgery bound in the four-independent-component QROM, with the reduction's own
hash evaluations included at each arity. -/
noncomputable def componentForgeryBound (q qs : ℕ) : ℝ≥0∞ :=
  let count := componentCounts S.vp qs
  epsUdSet S q + epsUdSet S q + itsrBound S.vp.params (q + count.itsr) qs +
    (epsDsprSet S (q + count.dspr) + 3 * epsTcrSet S (q + count.tcrFv)) +
    (epsTcrSet S (q + count.tcr1) + epsTcrSet S (q + count.tcr2) +
      epsTcrSet S (q + count.tcrLen) + epsTcrSet S (q + count.tcrK)) +
    ((S.vp.params.w - 2 : ℕ) : ℝ≥0∞) * epsUdSet S (q + count.ud) +
    epsPreSet S (q + count.pre) + epsTcrSet S (q + count.tcrT)

variable (c : Caps) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input S c) (Output S) E)

set_option maxHeartbeats 1200000 in
theorem suf_closed (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ht : max 2 (max S.vp.params.len S.vp.params.k) ≤ c.tl) :
    avg S c (fun g => qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤
      componentForgeryBound S q qs := by
  have hl := suf_linear S c rand seeds F
  simp only [qLinRealSufG, qLinIdealSufG, ← qLinearRealSide_eq_general, ← qLinearIdealSide_eq_general] at hl
  exact composeUniform S (rand := rand) (seeds := seeds) (fun (g : FinFns S.vp.params c) => g.toRand) (internal S c rand seeds F) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one)
    (fun g => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one) hl
    (suf_key_prf S c rand seeds F q hq) (suf_msg_prf S c rand seeds F q hq hc)
    (itsr_closed S c rand seeds F q qs hq hs hc)
    (dspr_term_closed S c rand seeds F (by omega) q qs hq hs)
    (tcrFv_term_closed S c rand seeds F (by omega) q qs hq hs)
    (class_tcr_le S c rand seeds F 1 (by omega) q qs hq hs)
    (class_tcr_le S c rand seeds F 2 (by omega) q qs hq hs)
    (class_tcr_le S c rand seeds F S.vp.params.len (by omega) q qs hq hs)
    (class_tcr_le S c rand seeds F S.vp.params.k (by omega) q qs hq hs)
    (ud_closed S c rand seeds F q qs (by omega) hq hs)
    (pre_closed S c rand seeds F q qs (by omega) hq hs)
    (tcrT_term_closed S c rand seeds F (by omega) q qs hq hs)

end Reduction.SetOracle

#print axioms Reduction.SetOracle.suf_closed
