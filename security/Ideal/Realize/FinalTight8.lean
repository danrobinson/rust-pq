import Ideal.Realize.FinalTight7
import Ideal.Realize.TcrLegsFine

/-!
# Eighth tightening: the message blocks of the single-block SM-TCR realisers are not charged
(`status/TIGHT.md` §9)

`_tight7` with three more legs bounded by the fine per-game bound `tcr_bound_fine`
(`Games/TcrFine.lean`): class TCR at arities `1` (`F`) and `2` (`H`) (answer-storing realiser,
`classTcrLeg_fine`) and the WOTS-chain TCR (`wotsTcrLeg_fine`).  Their raw second-phase caps are
`QTF = Tcr.qMT qf = qf + 86416` (was `qf + (qs+1)·(86419 + x)`) and `QWT = QU qf qs` (was
`QcWL`).

* `ideal_bound_core_legs8`, `suf/euf_ideal_bound_legs8`;
* `linT8 = QP + 2·QM + 3·QF + 2·QT + 2·QTF + 2·QW + QWT + 14·QU + 40`,
  `polyP8 = polyP7 + 3·(Qc + 40·N + 1)`;
* `QlinT8 qf qs ℓ = 27·qf + qs·(16771392 + 14·x) + 29487855 + 13·x`;
* `suf_ideal_closed_tight8`, `euf_ideal_closed_tight8` (same hypotheses as `suf_ideal_closed`);
  `tight8_le_tight7` (under the headline's own `QcAll ≤ 2^126`);
* points: `2^-77 + 2^-132 + 2^-63`, `2^-63 + 2^-94 + 2^-59`, `2^-45 + 2^-46 + 2^-39`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
attribute [local irreducible] Reduction.Lazy.sparseTable Reduction.Lazy.structSecIdx

/-! ## The composition with the `PRF`, `PRF_msg`, SM-UD and single-block SM-TCR legs as hypotheses -/

private theorem compose_arith8
    {adv r1 i1 a1 r2 i2 a2 c c' Ds S dv T T' X X' n R I aU p p' t t' : ℝ≥0∞}
    (h1 : r1 ≤ i1 + a1) (h2 : r2 ≤ i2 + a2) (h3 : Ds ≤ S + dv) (h4 : R ≤ I + aU)
    (hc : c ≤ c') (hT : T ≤ T') (hX : X ≤ X') (hp : p ≤ p') (ht : t ≤ t')
    (hfin : i1 + i2 + S + n * I ≠ ⊤)
    (h : adv + (i1 + i2 + S + n * I) ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t) :
    adv ≤ a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t' := by
  have h' : adv + (i1 + i2 + S + n * I) ≤
      (a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t') + (i1 + i2 + S + n * I) :=
    calc adv + (i1 + i2 + S + n * I)
        ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t := h
      _ ≤ (i1 + a1) + (i2 + a2) + c' + ((S + dv) + 3 * T') + X' + n * (I + aU) + p' + t' := by
          gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 h'

section Core

variable {pkSeedDist : ProbComp (Bytes 16)} {γ : ℝ≥0∞}

/-- **`ideal_bound_core_legs7` with the class-TCR `F`, `H` and WOTS-chain TCR legs as hypotheses too** (`e₆` any bound on the
averaged real-minus-ideal SM-UD gap; the realiser `RU` is used only to see that the averaged
ideal probability is at most `1`). -/
theorem ideal_bound_core_legs8 (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (a : CF St Blk → ℝ≥0∞)
    (B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y)
    (B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g)))
    (B₃ : ∀ g : CF St Blk, KeyedHash.ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))))
    (D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1))
    (C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2))
    (C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len))
    (C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k))
    (B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist))
    (hlin : ∀ g, a g + Reduction.linearIdealSide (B₁ g) (B₂ g) (D g) (B₆ g) ≤
      Reduction.linearRealSide pkSeedDist (B₁ g) (B₂ g) (B₃ g) (D g) (T g) (C₁ g) (C₂ g) (C₃ g)
        (C₄ g) (B₆ g) (B₇ g) (B₈ g))
    {εI : ℝ≥0∞} (hI : (cfAvg fun g => KeyedHash.ITSRAdvantage (B₃ g)) ≤ εI)
    {q qO : ℕ} (R₁ : RealizesPrf B₁ q qO)
    {qm qOm mlen : ℕ} (R₂ : RealizesMsg B₂ qm qOm mlen)
    {pD : P3} (RD : RealizesDspr pkSeedDist D pD) (hD : pD.q₂ ≤ 2 ^ 126)
    {pT : P3} (RT : RealizesForsTcr pkSeedDist T pT)
    {pF pH pL pK : P5} (RF : RealizesTcr pkSeedDist 1 C₁ pF) (RH : RealizesTcr pkSeedDist 2 C₂ pH)
    (RL : RealizesTcr pkSeedDist Link.vp.params.len C₃ pL)
    (RK : RealizesTcr pkSeedDist Link.vp.params.k C₄ pK)
    {pU pP pW : P5} (RU : RealizesUd pkSeedDist B₆ pU) (RP : RealizesPre pkSeedDist B₇ pP)
    (RW : RealizesWotsTcr pkSeedDist B₈ pW)
    {e₁ e₂ e₆ eF eH eW : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr (B₁ g)) ≤
      (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr (B₂ g)) ≤
      (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) + e₂)
    (h₆ : (cfAvg fun g => SM_DT_UD_RealSuccess (B₆ g)) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) + e₆)
    (hF : (cfAvg fun g => SM_DT_TCR_Advantage (C₁ g)) ≤ eF)
    (hH : (cfAvg fun g => SM_DT_TCR_Advantage (C₂ g)) ≤ eH)
    (hW : (cfAvg fun g => SM_DT_TCR_Advantage (B₈ g)) ≤ eW) :
    cfAvg a ≤ e₁ + e₂ + εI +
      (epsDspr γ pD + 3 * epsForsTcr γ pT) +
      (eF + eH + epsTcrLen γ pL + epsTcrK γ pK) +
      14 * e₆ + epsPre γ pP + eW := by
  have havg := cfAvg_mono hlin
  simp only [Reduction.linearIdealSide, Reduction.linearRealSide, cfAvg_add, cfAvg_mul_left]
    at havg
  rw [w_sub_two_128s] at havg
  have i1 : (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) ≤ 1 := by
    rw [show (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) = _ from cfAvg_of_evalDist_eq R₁.ideal]
    exact cfAdvantage_le_one _
  have i2 : (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) ≤ 1 := by
    rw [show (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) = _ from cfAvg_of_evalDist_eq R₂.ideal]
    exact cfAdvantage_le_one _
  have i3 : (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) ≤ 1 := by
    rw [show (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) = _ from
      cfAvg_of_evalDist_eq RD.sp]
    exact cfAdvantage_le_one _
  have i4 : (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) ≤ 1 := by
    rw [show (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) = _ from cfAvg_of_evalDist_eq RU.ideal]
    exact cfAdvantage_le_one _
  have hfin : (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) +
      (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) +
      (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) +
      ((14 : ℕ) : ℝ≥0∞) * (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨(i1.trans_lt ENNReal.one_lt_top).ne, (i2.trans_lt ENNReal.one_lt_top).ne⟩,
      (i3.trans_lt ENNReal.one_lt_top).ne⟩,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (i4.trans_lt ENNReal.one_lt_top).ne⟩
  have key := compose_arith8 h₁ h₂ (RD.bound hγ hD) h₆ hI (RT.bound hγ)
    (add_le_add (add_le_add (add_le_add hF hH)
      (RL.bound_len hγ len_128s)) (RK.bound_k hγ k_128s))
    (RP.bound hγ) hW hfin havg
  simpa using key

end Core

section Bundle

variable {pkSeedDist : ProbComp (Bytes 16)}
  {B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y}
  {B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g))}
  {D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1)}
  {C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2)}
  {C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len)}
  {C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k)}
  {B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist)}

/-- The sum of the explicit bounds, with the `PRF`, `PRF_msg`, SM-UD, class-TCR `F`, `H` and
WOTS-chain TCR terms replaced by `e₁`, `e₂`, `e₆`, `eF`, `eH`, `eW`. -/
noncomputable def Realizers.epsL8 (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    (e₁ e₂ e₆ eF eH eW γ : ℝ≥0∞) : ℝ≥0∞ :=
  e₁ + e₂ + (epsDspr γ R.pD + 3 * epsForsTcr γ R.pT) +
    (eF + eH + epsTcrLen γ R.pL + epsTcrK γ R.pK) +
    14 * e₆ + epsPre γ R.pP + eW

/-- The `2^-128` coefficient with the fine SM-UD and single-block SM-TCR legs. -/
def linT8 (QP QM QF QT QTF QW QWT QU : ℕ) : ℕ :=
  QP + 2 * QM + 3 * QF + 2 * QT + 2 * QTF + 2 * QW + QWT + 14 * QU + 40

/-- The `2^-256` part with the fine SM-UD and single-block SM-TCR legs. -/
def polyP8 (Qc N qs ℓ : ℕ) : ℕ := polyP7 Qc N qs ℓ + 3 * (Qc + 40 * N + 1)

theorem polyP8_mono {Qc N qs ℓ Qc' N' qs' ℓ' : ℕ} (h1 : Qc ≤ Qc') (h2 : N ≤ N') (h3 : qs ≤ qs')
    (h4 : ℓ ≤ ℓ') : polyP8 Qc N qs ℓ ≤ polyP8 Qc' N' qs' ℓ' := by
  unfold polyP8
  have := polyP7_mono h1 h2 h3 h4
  omega

/-- **`Realizers.epsL_le_tight` with the fine SM-UD and single-block SM-TCR legs.** -/
theorem Realizers.epsL8_le_tight (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    {Qc N qs ℓ QP QM QF QT QTF QW QWT QU qPM qMM qUM qFM qHM qWM : ℕ} (h : R.Le Qc N qs ℓ)
    (hP : qPM ≤ QP) (hM : qMM ≤ QM)
    (hD : R.pD.q₁ = 0) (hT : R.pT.q₁ = 0) (hT2 : R.pT.q₂ ≤ QF)
    (hF : R.pF.q₁ = 0) (hF2 : qFM ≤ QTF) (hH : R.pH.q₁ = 0) (hH2 : qHM ≤ QTF)
    (hL : R.pL.q₁ = 0) (hL2 : R.pL.q₂ ≤ QT) (hK : R.pK.q₁ = 0) (hK2 : R.pK.q₂ ≤ QT)
    (hU : R.pU.q₁ = 0) (hU2 : qUM ≤ QU) (hR : R.pP.q₁ = 0) (hR2 : R.pP.q₂ ≤ QW)
    (hW : R.pW.q₁ = 0) (hW2 : qWM ≤ QWT) :
    R.epsL8 (epsPrfM qPM R.q R.qO) (epsMsgM qMM R.qm R.qOm R.mlen) (epsUdF γu R.pU qUM)
        (epsTcrF γu R.pF qFM) (epsTcrF γu R.pH qHM) (epsTcrF γu R.pW qWM) γu ≤
      nf (linT8 QP QM QF QT QTF QW QWT QU) (polyP8 Qc N qs ℓ) := by
  have e : nf (linT8 QP QM QF QT QTF QW QWT QU) (polyP8 Qc N qs ℓ) =
      nf QP ((Qc + N) ^ 2) + nf (2 * QM) ((Qc + qs * (ℓ + 1) + 2) ^ 2) +
      (nf 0 (4 * Qc + 2 * N + 3) + 3 * nf (QF + 1) (2 * Qc + N + 2)) +
      (nf (QTF + 1) (2 * Qc + 42 * N + 2 + (Qc + 40 * N + 1)) +
        nf (QTF + 1) (2 * Qc + 42 * N + 2 + (Qc + 40 * N + 1)) +
        nf (QT + 22) (18 * (2 * Qc + 22 * N + 21) ^ 2 + 2 * Qc + 42 * N + 1) +
        nf (QT + 10) (18 * (2 * Qc + 22 * N + 9) ^ 2 + 2 * Qc + 42 * N + 1)) +
      14 * nf QU (4 * Qc + 84 * N + 2 + (20 * N + 1)) + nf (2 * (QW + 1)) (2 * Qc + 42 * N + 2) +
      nf (QWT + 1) (2 * Qc + 42 * N + 2 + (Qc + 40 * N + 1)) := by
    unfold nf polyP8 polyP7 polyP linT8
    push_cast
    ring
  rw [e]
  unfold Realizers.epsL8
  gcongr
  · exact epsPrfM_le_t hP h.q h.qO
  · exact epsMsgM_le_t hM h.qm h.qOm h.mlen
  · exact epsDspr_le_t h.pD hD
  · exact epsForsTcr_le_t h.pT hT hT2
  · exact epsTcrF_le_t h.pF hF hF2
  · exact epsTcrF_le_t h.pH hH hH2
  · exact epsTcrLen_le_t h.pL hL hL2
  · exact epsTcrK_le_t h.pK hK hK2
  · exact epsUdF_le_t h.pU hU hU2
  · exact epsPre_le_t h.pP hR hR2
  · exact epsTcrF_le_t h.pW hW hW2

end Bundle

section Legs

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}
  {pkSeedDist : ProbComp (Bytes 16)}

/-- `suf_ideal_bound_legs` with the SM-UD, class-TCR `F`, `H` and WOTS-chain TCR legs as hypotheses. -/
theorem suf_ideal_bound_legs8 {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrSufI S optRand pkSeedDist ≤ εI)
    (R : SufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) {e₁ e₂ e₆ eF eH eW : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr
        (Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.prfIdealPr
        (Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr
        (Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.msgIdealPr
        (Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))) + e₂)
    (h₆ : (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))) + e₆)
    (hF : (cfAvg fun g => SM_DT_TCR_Advantage
        (Reduction.bTcrArM 1 (S.typedS optRand pkSeedDist g))) ≤ eF)
    (hH : (cfAvg fun g => SM_DT_TCR_Advantage
        (Reduction.bTcrArM 2 (S.typedS optRand pkSeedDist g))) ≤ eH)
    (hW : (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))) ≤ eW) :
    sufI S optRand pkSeedDist ≤ εI + R.epsL8 e₁ e₂ e₆ eF eH eW γ := by
  rw [sufI_eq_cfAvg]
  refine (ideal_bound_core_legs8 hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_suf_cma_linear (structuralG g) (S.sufInst optRand pkSeedDist g))
    hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK R.ud R.pre R.wotsTcr
    h₁ h₂ h₆ hF hH hW).trans (le_of_eq ?_)
  unfold Realizers.epsL8
  ring

/-- `euf_ideal_bound_legs` with the SM-UD, class-TCR `F`, `H` and WOTS-chain TCR legs as hypotheses. -/
theorem euf_ideal_bound_legs8 {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrEufI S optRand pkSeedDist ≤ εI)
    (R : EufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) {e₁ e₂ e₆ eF eH eW : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr
        (Reduction.bPrfC (S.typedE optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.prfIdealPr
        (Reduction.bPrfC (S.typedE optRand pkSeedDist g))) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr
        (Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.msgIdealPr
        (Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))) + e₂)
    (h₆ : (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))) + e₆)
    (hF : (cfAvg fun g => SM_DT_TCR_Advantage
        (Reduction.bTcrArM 1 (S.typedE optRand pkSeedDist g))) ≤ eF)
    (hH : (cfAvg fun g => SM_DT_TCR_Advantage
        (Reduction.bTcrArM 2 (S.typedE optRand pkSeedDist g))) ≤ eH)
    (hW : (cfAvg fun g => SM_DT_TCR_Advantage (Reduction.rTcrT pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))) ≤ eW) :
    eufI S optRand pkSeedDist ≤ εI + R.epsL8 e₁ e₂ e₆ eF eH eW γ := by
  rw [eufI_eq_cfAvg]
  refine (ideal_bound_core_legs8 hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_euf_cma_linear (structuralG g) (S.eufInst optRand pkSeedDist g))
    hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK R.ud R.pre R.wotsTcr
    h₁ h₂ h₆ hF hH hW).trans (le_of_eq ?_)
  unfold Realizers.epsL8
  ring

end Legs

/-! ## The coefficient -/

/-- **The `2^-128` coefficient with the SM-UD and single-block SM-TCR realisers' message blocks
uncharged**: `27` per forger compression query; per signing query `16771392` and `14` per message
block; one-off `29487855 + 13` per message block. -/
def QlinT8 (qf qs ℓ : ℕ) : ℕ :=
  27 * qf + qs * (16771392 + 14 * ((ℓ + 56) / 64)) + 29487855 + 13 * ((ℓ + 56) / 64)

theorem qMT_eq (qf : ℕ) : Tcr.qMT qf = qf + 86416 := by
  have h3 := Reduction.Resources2.verifyHashes_128s
  have h4 : thashCost Tcr.Bmax = 11 := by decide
  unfold Tcr.qMT
  rw [h3, h4]
  ring

theorem qMW_le_QU (qf qs : ℕ) : Wots.qMW qf qs ≤ QU qf qs := by
  have h1 := Wots.tcrH_le qs
  have h2 := Wots.tcrLg_le qs
  unfold Wots.qMW QU
  omega

theorem linT8_le_QlinT8 (qf qs ℓ : ℕ) :
    linT8 (qf + (qs + 1) * (32272 + 2 * ((ℓ + 56) / 64)))
      (qf + (qs + 1) * (39438 + (ℓ + 56) / 64))
      (qf + 544286 + 3932321 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3))
      (qf + (qs + 1) * (86419 + (ℓ + 56) / 64)) (qf + 86416)
      (Wots.QcWL qf qs ℓ) (QU qf qs) (QU qf qs) ≤ QlinT8 qf qs ℓ := by
  unfold linT8 QlinT8 Wots.QcWL QU
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

/-- `QlinT8` is `QlinT7` minus the class-TCR (`F`, `H`) per-signature counts and the WOTS-chain
TCR realiser's `H_msg` cost. -/
theorem QlinT8_add (qf qs ℓ : ℕ) :
    QlinT8 qf qs ℓ + (172841 * qs + 3 * qs * ((ℓ + 56) / 64) + 4 * ((ℓ + 56) / 64) + 12) =
      QlinT7 qf qs ℓ := by
  unfold QlinT8 QlinT7
  generalize (ℓ + 56) / 64 = x
  ring

theorem QlinT8_le_QlinT7 (qf qs ℓ : ℕ) : QlinT8 qf qs ℓ ≤ QlinT7 qf qs ℓ := by
  have := QlinT8_add qf qs ℓ
  omega

section Tight8

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem sufRealizers8_epsL_le :
    (sufRealizers5 S oR hqf hqs hlong hout).epsL8
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ)
        (epsUdF γu (Wots.pUL qf qs ℓ) (Wots.qMU qf qs))
        (epsTcrF γu (Tcr.tcrP3 qf qs ℓ) (Tcr.qMT qf)) (epsTcrF γu (Tcr.tcrP3 qf qs ℓ) (Tcr.qMT qf))
        (epsTcrF γu (Wots.pWL qf qs ℓ) (Wots.qMW qf qs)) γu ≤
      nf (QlinT8 qf qs ℓ) (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((sufRealizers5 S oR hqf hqs hlong hout).epsL8_le_tight
    (sufRealizers5_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2ForsL_eq qf qs ℓ).le
    rfl (qMT_eq qf).le rfl (qMT_eq qf).le rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (qMU_le_QU qf qs) rfl (Wots.pPL_le qf qs ℓ).2.2.2.2
    rfl (qMW_le_QU qf qs)).trans
    (nf_mono (linT8_le_QlinT8 qf qs ℓ) le_rfl)

theorem eufRealizers8_epsL_le :
    (eufRealizers5 S oR hqf hqs hlong hout).epsL8
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ)
        (epsUdF γu (Wots.pUL qf qs ℓ) (Wots.qMU qf qs))
        (epsTcrF γu (Tcr.tcrP3 qf qs ℓ) (Tcr.qMT qf)) (epsTcrF γu (Tcr.tcrP3 qf qs ℓ) (Tcr.qMT qf))
        (epsTcrF γu (Wots.pWL qf qs ℓ) (Wots.qMW qf qs)) γu ≤
      nf (QlinT8 qf qs ℓ) (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((eufRealizers5 S oR hqf hqs hlong hout).epsL8_le_tight
    (eufRealizers5_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2ForsL_eq qf qs ℓ).le
    rfl (qMT_eq qf).le rfl (qMT_eq qf).le rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (qMU_le_QU qf qs) rfl (Wots.pPL_le qf qs ℓ).2.2.2.2
    rfl (qMW_le_QU qf qs)).trans
    (nf_mono (linT8_le_QlinT8 qf qs ℓ) le_rfl)

/-- The SUF bound from any bound `εI` on the ITSR term. -/
theorem suf_tight8_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrSufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT8 qf qs ℓ) (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (suf_ideal_bound_legs8 hγ_uniform hI (sufRealizers5 S oR hqf hqs hlong hout)
    ((sufRealizers5_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfSuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfSuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgSuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgSuf_mark S oR _ hqf hqs hlong hout))
    (udLeg_fine hγ_uniform hqf hqs hlong hout)
    (classTcrLeg_fine hγ_uniform hqf hqs hlong hout 1 (Or.inl rfl))
    (classTcrLeg_fine hγ_uniform hqf hqs hlong hout 2 (Or.inr rfl))
    (wotsTcrLeg_fine hγ_uniform hqf hqs hlong hout)).trans
    (add_le_add le_rfl (sufRealizers8_epsL_le S oR hqf hqs hlong hout))

/-- The EUF bound from any bound `εI` on the ITSR term. -/
theorem euf_tight8_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrEufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT8 qf qs ℓ) (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (euf_ideal_bound_legs8 hγ_uniform hI (eufRealizers5 S oR hqf hqs hlong hout)
    ((eufRealizers5_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfEuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfEuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgEuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgEuf_mark S oR _ hqf hqs hlong hout))
    (udLeg_fineE hγ_uniform hqf hqs hlong hout)
    (classTcrLeg_fineE hγ_uniform hqf hqs hlong hout 1 (Or.inl rfl))
    (classTcrLeg_fineE hγ_uniform hqf hqs hlong hout 2 (Or.inr rfl))
    (wotsTcrLeg_fineE hγ_uniform hqf hqs hlong hout)).trans
    (add_le_add le_rfl (eufRealizers8_epsL_le S oR hqf hqs hlong hout))

end Tight8

/-! ## The headlines -/

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only, with
shape marking for `PRF`/`PRF_msg`, answer-storing class-TCR realisers, per-arity FORS and WOTS
counts, message blocks per signing query, and the `H_msg` chains of the SM-UD and single-block
SM-TCR realisers uncharged.**  Same hypotheses as `suf_ideal_closed`; the `2^-128` coefficient is
`QlinT8 qf qs ℓ = 27·qf + qs·(16771392 + 14·x) + 29487855 + 13·x` (`QlinT8_le_QlinT7`), the
`2^-256` part `polyP8 = polyP7 + 3·(QcAll + 40·NAll qs + 1)`. -/
theorem suf_ideal_closed_tight8 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact suf_tight8_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrSufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- **EUF-CMA analogue of `suf_ideal_closed_tight8`.** -/
theorem euf_ideal_closed_tight8 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact euf_tight8_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrEufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- The right-hand side of `suf_ideal_closed_tight8` is at most that of
`suf_ideal_closed_tight7`, under the headline's hypothesis `QcAll qf qs ℓ ≤ 2^126`: the `2^-128`
coefficient loses `172841·qs + 3·qs·x + 4·x + 12`, the `2^-256` part gains
`3·(QcAll + 40·NAll + 1) ≤ 12·2^128`. -/
theorem tight8_le_tight7 (qf qs ℓ : ℕ) (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT7 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc, add_assoc]
  refine add_le_add le_rfl ?_
  rw [← QlinT8_add qf qs ℓ]
  unfold polyP8
  set a := QlinT8 qf qs ℓ
  set b := 172841 * qs + 3 * qs * ((ℓ + 56) / 64) + 4 * ((ℓ + 56) / 64) + 12
  set P := polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)
  have hN : 3 * (QcAll qf qs ℓ + 40 * NAll qs + 1) ≤ 2 ^ 128 * b := by
    have h1 := NAll_le_lin qs
    have h2 : 12 + 172841 * qs ≤ b := by omega
    nlinarith
  have e1 : ((2 : ℝ≥0∞) ^ 256) = 2 ^ 128 * 2 ^ 128 := by rw [← pow_add]
  have key : ((3 * (QcAll qf qs ℓ + 40 * NAll qs + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((b : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
    rw [e1, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), mul_assoc]
    gcongr
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp)]
    exact_mod_cast hN
  calc ((a : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((P + 3 * (QcAll qf qs ℓ + 40 * NAll qs + 1) : ℕ) : ℝ≥0∞) /
        2 ^ 256
      = (a : ℝ≥0∞) / 2 ^ 128 + (P : ℝ≥0∞) / 2 ^ 256 +
          ((3 * (QcAll qf qs ℓ + 40 * NAll qs + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        push_cast; rw [ENNReal.add_div]; ring
    _ ≤ (a : ℝ≥0∞) / 2 ^ 128 + (P : ℝ≥0∞) / 2 ^ 256 + ((b : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
        gcongr
    _ = _ := by push_cast; rw [ENNReal.add_div]; ring

/-! ## Numerics -/

theorem QlinT8_le {qf qs ℓ F₀ S₀ : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀) (hℓ : ℓ ≤ 2 ^ 26) :
    QlinT8 qf qs ℓ ≤ 27 * F₀ + S₀ * (16771392 + 14 * 2 ^ 20) + 29487855 + 13 * 2 ^ 20 := by
  have := div64_le_2_20 hℓ
  unfold QlinT8
  gcongr

theorem eleven_tight8_le {qf qs ℓ F₀ S₀ Qc₀ N₀ k m : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hnum : (27 * F₀ + S₀ * (16771392 + 14 * 2 ^ 20) + 29487855 + 13 * 2 ^ 20) * 2 ^ 128 +
      polyP8 Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m) :
    nf (QlinT8 qf qs ℓ) (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (nf_mono (QlinT8_le hf hs hℓ) (polyP8_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow k m hkm hnum)

theorem eleven_tight8_le2 {qf qs ℓ F₀ S₀ Qc₀ N₀ k m k' m' : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hkm' : m' + k' = 256)
    (hnum : (27 * F₀ + S₀ * (16771392 + 14 * 2 ^ 20) + 29487855 + 13 * 2 ^ 20) * 2 ^ 128 +
      polyP8 Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m + 2 ^ m') :
    nf (QlinT8 qf qs ℓ) (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤
      ((2 : ℝ≥0∞) ^ k)⁻¹ + ((2 : ℝ≥0∞) ^ k')⁻¹ :=
  (nf_mono (QlinT8_le hf hs hℓ) (polyP8_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow2 k m k' m' hkm hkm' hnum)

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD and single-block SM-TCR message blocks uncharged, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_closed_tight8_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 60 + 2 ^ 46 := QcAll_le_of hs hℓ (Nat.add_le_add hf (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 60) (2 ^ 21) (2 ^ 60) (2007387 * 2 ^ 20) (2 ^ 20 + 1) (2 ^ 20) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight8_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight8_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP8 polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD and single-block SM-TCR message blocks uncharged, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-59`. -/
theorem suf_ideal_closed_tight8_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight8_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight8_le hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) rfl
      (by unfold polyP8 polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD and single-block SM-TCR message blocks uncharged, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + 2^-39`. -/
theorem suf_ideal_closed_tight8_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight8_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight8_le hf hs hℓ hQc (NAll_le_82 hs) (k := 39) (m := 217)
      rfl (by unfold polyP8 polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD and single-block SM-TCR message blocks uncharged, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_closed_tight8_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 60 + 2 ^ 46 := QcAll_le_of hs hℓ (Nat.add_le_add hf (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 60) (2 ^ 21) (2 ^ 60) (2007387 * 2 ^ 20) (2 ^ 20 + 1) (2 ^ 20) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight8_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight8_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP8 polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD and single-block SM-TCR message blocks uncharged, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-59`. -/
theorem euf_ideal_closed_tight8_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight8_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight8_le hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) rfl
      (by unfold polyP8 polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD and single-block SM-TCR message blocks uncharged, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + 2^-39`. -/
theorem euf_ideal_closed_tight8_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight8_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight8_le hf hs hℓ hQc (NAll_le_82 hs) (k := 39) (m := 217)
      rfl (by unfold polyP8 polyP7 polyP; norm_num)))


end Ideal

#print axioms Ideal.linT8_le_QlinT8
#print axioms Ideal.QlinT8_le_QlinT7
#print axioms Ideal.QlinT8_add
#print axioms Ideal.ideal_bound_core_legs8
#print axioms Ideal.Realizers.epsL8_le_tight
#print axioms Ideal.suf_ideal_closed_tight8
#print axioms Ideal.euf_ideal_closed_tight8
#print axioms Ideal.tight8_le_tight7
#print axioms Ideal.suf_ideal_closed_tight8_2_20
#print axioms Ideal.suf_ideal_closed_tight8_2_40
#print axioms Ideal.suf_ideal_closed_tight8_2_64
#print axioms Ideal.euf_ideal_closed_tight8_2_20
#print axioms Ideal.euf_ideal_closed_tight8_2_40
#print axioms Ideal.euf_ideal_closed_tight8_2_64
