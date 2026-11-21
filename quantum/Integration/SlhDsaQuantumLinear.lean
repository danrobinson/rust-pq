import Integration.SlhDsaQuantumTight
import Reduction.Linear

/-!
# SLH-DSA against quantum forgers: memoising class adversaries and the linear (signed) form

NOT part of the default target; checked by `scripts/check-integration.sh`.

Quantum-machine versions of

* the `_memo` headlines of `security/Reduction/TcrMemoHeadline.lean` (tight caps, class
  adversaries `bTcrArM n` without structure recomputation):
  `slhdsa_{euf,suf}_cma_final_memo_quantum`, `slhdsa_pure_{euf,suf}_cma_final_memo_quantum`;
* the linear headlines of `security/Reduction/Linear.lean`
  (`Adv + Pr[ideal worlds] ≤ Pr[real worlds] + search advantages`):
  `slhdsa_{euf,suf}_cma_final_linear_quantum`, `slhdsa_pure_{euf,suf}_cma_final_linear_quantum`.

Every term on both sides is a Born probability (`qWeight`) of an explicit quantum machine that
runs the quantum forger once.  Hypothesis: `RationalBorn`.

New machine: `qbTcrArM n Q` ("`bTcrArM n`'s code around `Q`").
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

/-! ## The memoising class adversaries -/

/-- Phase 2 of `bTcrArM n` around the quantum forger (`Reduction.memoForge`): the forger is run
once against the `G2` signing oracle of the table; the collision is looked up classically in the
stored list. -/
noncomputable def qMemoForge (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    Closed W (ℕ × {xs : List prims.Y // xs.length = n}) :=
  close ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
      g2SignOracle optRand (idealPk vp prims s.1 pkSeed)
        (fun m R => idealSign vp prims s.1 m (idealPk vp prims s.1 pkSeed) R))
    (Q.main (idealPk vp prims s.1 pkSeed)) [] >>= fun z =>
  liftU (pure (classOut prims n s.2
    ((findCollisionM pkSeed s.2 (verifyCalls (idealPk vp prims s.1 pkSeed) z.1.1 z.1.2)).getD
      (0, []))))

theorem toProbCompC_qMemoForge (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    toProbCompC (qMemoForge n Q s pkSeed) Q.ρ₀ = (bTcrArM n Q.toClassical).forge s pkSeed := by
  rw [qMemoForge, toProbCompC_bind_liftU, toProbCompC_close _ (forwardsUnif_ofLift_add _),
    bTcrArM_forge]
  rfl

/-- The quantum arity-`n` SM-TCR adversary at the tight cap without structure recomputation,
"`bTcrArM n`'s code around `Q`". -/
noncomputable def qbTcrArM (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    QSM_DT_TCR_Adversary W (thashArityProblemT vp prims pkSeedDist n) :=
  qTcrOfClassical (bTcrArM n Q.toClassical) (fun s pk => qMemoForge n Q s pk) Q.ρ₀
    Q.posSemidef Q.trace_eq_one

theorem toClassical_qbTcrArM (n : ℕ) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qbTcrArM n Q).toClassical = bTcrArM n Q.toClassical :=
  toClassical_qTcrOfClassical _ _ _ _ _ fun s pk => toProbCompC_qMemoForge n Q s pk

theorem qSM_DT_TCR_Advantage_qbTcrArM (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qSM_DT_TCR_Advantage (qbTcrArM n Q) = SM_DT_TCR_Advantage (bTcrArM n Q.toClassical) := by
  have hR : ∀ st pk, RationalBorn ((qbTcrArM n Q).forge st pk) (qbTcrArM n Q).ρ₀ :=
    fun st pk ↦ rationalBorn_bind_liftU _ _ _ (rationalBorn_close _ _ _ _ (hQ _))
  rw [qSM_DT_TCR_Advantage_eq (qbTcrArM n Q) hR, toClassical_qbTcrArM]

/-! ## The memo bound with quantum advantages -/

/-- The tight-cap bound with the memoising class adversaries, every term a quantum advantage of
an explicit quantum machine running `Q` once; `P₁`, `P₂` are the two PRF terms. -/
noncomputable def qBoundMemo (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (P₁ P₂ : ℝ≥0∞) : ℝ≥0∞ :=
  P₁ + P₂ +
    qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
    (qDsprFV_Advantage (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
    (qSM_DT_TCR_Advantage (qbTcrArM 1 Q) + qSM_DT_TCR_Advantage (qbTcrArM 2 Q) +
      qSM_DT_TCR_Advantage (qbTcrArM vp.params.len Q) +
      qSM_DT_TCR_Advantage (qbTcrArM vp.params.k Q)) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_Advantage (qrUd Q) +
    qSM_DT_PRE_Advantage (qrPre Q) +
    qSM_DT_TCR_Advantage (qrTcrT Q)

/-- EUF-CMA: PRF distinguishers `qbPrfC Q`, `qbPrfMsgL Q`. -/
noncomputable def qBetaEufMemo (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ℝ≥0∞ :=
  qBoundMemo Q (qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀)
    (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀)

/-- SUF-CMA: PRF distinguishers `qbPrfWC sufCheck Q`, `qbPrfMsgWL sufCheck Q`. -/
noncomputable def qBetaSufMemo (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ℝ≥0∞ :=
  qBoundMemo Q (qPrfAdvantage (skPrfC vp prims) (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgWL sufCheck Q) Q.ρ₀)

theorem boundFinalMemo_toClassical (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL Q.toClassical)
        (toDspr (Lazy.bOpenPreS Q.toClassical)) (toTcr (Lazy.bOpenPreS Q.toClassical))
        (bTcrArM 1 Q.toClassical) (bTcrArM 2 Q.toClassical)
        (bTcrArM vp.params.len Q.toClassical) (bTcrArM vp.params.k Q.toClassical)
        (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)) (rPre pkSeedDist (Lazy.bWotsS Q.toClassical))
        (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)) =
      qBoundMemo Q ((skPrfC vp prims).prfAdvantage B₁) ((msgPrf vp prims).prfAdvantage B₂) := by
  unfold boundFinalTight qBoundMemo
  rw [qItsrAdvantage_qbItsrL Q hQ, qDsprFV_Advantage_qToDspr Q hQ, qTcrFV_Advantage_qToTcr Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArM 1 Q hQ, qSM_DT_TCR_Advantage_qbTcrArM 2 Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArM vp.params.len Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArM vp.params.k Q hQ, qSM_DT_UD_Advantage_qrUd Q hQ,
    qSM_DT_PRE_Advantage_qrPre Q hQ, qSM_DT_TCR_Advantage_qrTcrT Q hQ]

theorem betaEufFinalMemo_toClassical (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    betaEufFinalMemo Q.toClassical = qBetaEufMemo Q := by
  unfold betaEufFinalMemo qBetaEufMemo
  rw [boundFinalMemo_toClassical Q hQ, qPrfAdvantage_qbPrfC Q hQ, qPrfAdvantage_qbPrfMsgL Q hQ]

theorem betaSufFinalMemo_toClassical (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    betaSufFinalMemo Q.toClassical = qBetaSufMemo Q := by
  unfold betaSufFinalMemo qBetaSufMemo
  rw [boundFinalMemo_toClassical Q hQ, qPrfAdvantage_qbPrfWC sufCheck Q hQ,
    qPrfAdvantage_qbPrfMsgWL sufCheck Q hQ]

/-- **EUF-CMA of SLH-DSA (internal algorithms) against quantum forgers: tight caps, memoising
class adversaries, quantum reduction adversaries.** -/
theorem slhdsa_euf_cma_final_memo_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo Q := by
  rw [← betaEufFinalMemo_toClassical Q hQ]
  exact qUnforgeableAdvantage_le_of_forall Q hQ betaEufFinalMemo (slhdsa_euf_cma_final_memo' hS)

/-- **SUF-CMA of SLH-DSA (internal algorithms) against quantum forgers: tight caps, memoising
class adversaries, quantum reduction adversaries.** -/
theorem slhdsa_suf_cma_final_memo_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo Q := by
  rw [← betaSufFinalMemo_toClassical Q hQ]
  exact qStrongUnforgeableAdvantage_le_of_forall Q hQ
    (fun S ↦ betaSufFinalMemo S.toUnforgeableAdversary) (slhdsa_suf_cma_final_memo' hS)

/-- **EUF-CMA of the external pure interface against quantum forgers (memo form).** -/
theorem slhdsa_pure_euf_cma_final_memo_quantum (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qToInternal Q) := by
  rw [← betaEufFinalMemo_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    toClassical_qToInternal]
  exact qUnforgeableAdvantage_le_of_forall Q hQ (fun A ↦ betaEufFinalMemo (toInternal A))
    (slhdsa_pure_euf_cma_final_memo' hS)

/-- **SUF-CMA of the external pure interface against quantum forgers (memo form).** -/
theorem slhdsa_pure_suf_cma_final_memo_quantum (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qToInternal Q) := by
  rw [← betaSufFinalMemo_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    toClassical_qToInternal]
  exact qStrongUnforgeableAdvantage_le_of_forall Q hQ
    (fun S ↦ betaSufFinalMemo (toInternal S.toUnforgeableAdversary))
    (slhdsa_pure_suf_cma_final_memo' hS)

/-! ## The linear form -/

/-- **Ideal side of the linear bound, quantum**: Born probabilities of output `true` in the ideal
worlds of the four distinguishing games; `I₁`, `I₂` are the two PRF terms. -/
noncomputable def qLinearIdealSide (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (I₁ I₂ : ℝ≥0∞) : ℝ≥0∞ :=
  I₁ + I₂ + qDsprFV_SPProbability (qToDspr Q) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_IdealSuccess (qrUd Q)

/-- **Real side of the linear bound, quantum**: `qBoundMemo` with each distinguishing advantage
replaced by the Born probability of the real world of its pair; `R₁`, `R₂` are the two PRF
terms. -/
noncomputable def qLinearRealSide (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (R₁ R₂ : ℝ≥0∞) : ℝ≥0∞ :=
  R₁ + R₂ +
    qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
    (qDsprFV_Success (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
    (qSM_DT_TCR_Advantage (qbTcrArM 1 Q) + qSM_DT_TCR_Advantage (qbTcrArM 2 Q) +
      qSM_DT_TCR_Advantage (qbTcrArM vp.params.len Q) +
      qSM_DT_TCR_Advantage (qbTcrArM vp.params.k Q)) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_RealSuccess (qrUd Q) +
    qSM_DT_PRE_Advantage (qrPre Q) +
    qSM_DT_TCR_Advantage (qrTcrT Q)

/-- EUF-CMA sides: PRF distinguishers `qbPrfC Q`, `qbPrfMsgL Q`. -/
noncomputable def qLinIdealEuf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearIdealSide Q (qPrfIdealPr (qbPrfC Q) Q.ρ₀) (qPrfIdealPr (qbPrfMsgL Q) Q.ρ₀)

noncomputable def qLinRealEuf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearRealSide Q (qPrfRealPr (skPrfC vp prims) (qbPrfC Q) Q.ρ₀)
    (qPrfRealPr (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀)

/-- SUF-CMA sides: PRF distinguishers `qbPrfWC sufCheck Q`, `qbPrfMsgWL sufCheck Q`. -/
noncomputable def qLinIdealSuf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearIdealSide Q (qPrfIdealPr (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfIdealPr (qbPrfMsgWL sufCheck Q) Q.ρ₀)

noncomputable def qLinRealSuf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearRealSide Q (qPrfRealPr (skPrfC vp prims) (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfRealPr (msgPrf vp prims) (qbPrfMsgWL sufCheck Q) Q.ρ₀)

section sides

variable (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
  (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀)
include hQ

theorem rationalBorn_qToDspr_guess
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pk : prims.PkSeed) : RationalBorn ((qToDspr Q).guess st pk) (qToDspr Q).ρ₀ :=
  rationalBorn_bind_liftU _ _ _ (rationalBorn_qFindRun Q hQ st pk)

theorem rationalBorn_qrUd_distinguish
    (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
      List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    RationalBorn ((qrUd Q).distinguish st pk) (qrUd Q).ρ₀ :=
  rationalBorn_bind_liftU _ _ _ (rationalBorn_qWotsForge Q hQ st.1 pk)

theorem linearIdealSide_toClassical
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    linearIdealSide B₁ B₂ (toDspr (Lazy.bOpenPreS Q.toClassical))
        (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)) =
      qLinearIdealSide Q (prfIdealPr B₁) (msgIdealPr B₂) := by
  unfold linearIdealSide qLinearIdealSide
  rw [qDsprFV_SPProbability_eq (qToDspr Q) (rationalBorn_qToDspr_guess Q hQ),
    toClassical_qToDspr, qSM_DT_UD_IdealSuccess_eq (qrUd Q) (rationalBorn_qrUd_distinguish Q hQ),
    toClassical_qrUd]

theorem linearRealSide_toClassical
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    linearRealSide pkSeedDist B₁ B₂ (Lazy.bItsrL Q.toClassical)
        (toDspr (Lazy.bOpenPreS Q.toClassical)) (toTcr (Lazy.bOpenPreS Q.toClassical))
        (bTcrArM 1 Q.toClassical) (bTcrArM 2 Q.toClassical)
        (bTcrArM vp.params.len Q.toClassical) (bTcrArM vp.params.k Q.toClassical)
        (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)) (rPre pkSeedDist (Lazy.bWotsS Q.toClassical))
        (rTcrT pkSeedDist (Lazy.bWotsS Q.toClassical)) =
      qLinearRealSide Q (prfRealPr B₁) (msgRealPr B₂) := by
  unfold linearRealSide qLinearRealSide
  rw [qItsrAdvantage_qbItsrL Q hQ,
    qDsprFV_Success_eq (qToDspr Q) (rationalBorn_qToDspr_guess Q hQ), toClassical_qToDspr,
    qTcrFV_Advantage_qToTcr Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArM 1 Q hQ, qSM_DT_TCR_Advantage_qbTcrArM 2 Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArM vp.params.len Q hQ,
    qSM_DT_TCR_Advantage_qbTcrArM vp.params.k Q hQ,
    qSM_DT_UD_RealSuccess_eq (qrUd Q) (rationalBorn_qrUd_distinguish Q hQ), toClassical_qrUd,
    qSM_DT_PRE_Advantage_qrPre Q hQ, qSM_DT_TCR_Advantage_qrTcrT Q hQ]

theorem linIdealEuf_toClassical : linIdealEuf Q.toClassical = qLinIdealEuf Q := by
  unfold linIdealEuf qLinIdealEuf
  rw [linearIdealSide_toClassical Q hQ, prfIdealPr, msgIdealPr,
    qPrfIdealPr_eq _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfC Q hQ),
    qPrfIdealPr_eq _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfMsgL Q hQ),
    toProbComp_qbPrfC, toProbComp_qbPrfMsgL]

theorem linRealEuf_toClassical : linRealEuf Q.toClassical = qLinRealEuf Q := by
  unfold linRealEuf qLinRealEuf
  rw [linearRealSide_toClassical Q hQ, prfRealPr, msgRealPr,
    qPrfRealPr_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfC Q hQ),
    qPrfRealPr_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfMsgL Q hQ),
    toProbComp_qbPrfC, toProbComp_qbPrfMsgL]

theorem rationalBorn_qbPrfWC (w : WinCheck vp prims) : RationalBorn (qbPrfWC w Q) Q.ρ₀ :=
  rationalBorn_wrap0 _ _ _ (rationalBorn_qbPrfW w Q hQ)

theorem rationalBorn_qbPrfMsgWL (w : WinCheck vp prims) : RationalBorn (qbPrfMsgWL w Q) Q.ρ₀ :=
  rationalBorn_qLazyRun _ _ _ <|
    rationalBorn_liftQ_bind _ _ _ fun _ ↦ rationalBorn_liftQ_bind _ _ _ fun _ ↦
      rationalBorn_bind_liftQ _ _ _ (rationalBorn_wrap _ _ _ _ (hQ _))

theorem linIdealSuf_toClassical : linIdealSuf Q.toClassical = qLinIdealSuf Q := by
  unfold linIdealSuf qLinIdealSuf
  rw [linearIdealSide_toClassical Q hQ, prfIdealPr, msgIdealPr,
    qPrfIdealPr_eq _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfWC Q hQ sufCheck),
    qPrfIdealPr_eq _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfMsgWL Q hQ sufCheck),
    toProbComp_qbPrfWC, toProbComp_qbPrfMsgWL]

theorem linRealSuf_toClassical : linRealSuf Q.toClassical = qLinRealSuf Q := by
  unfold linRealSuf qLinRealSuf
  rw [linearRealSide_toClassical Q hQ, prfRealPr, msgRealPr,
    qPrfRealPr_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfWC Q hQ sufCheck),
    qPrfRealPr_eq _ _ _ Q.posSemidef Q.trace_eq_one (rationalBorn_qbPrfMsgWL Q hQ sufCheck),
    toProbComp_qbPrfWC, toProbComp_qbPrfMsgWL]

end sides

/-- **EUF-CMA of SLH-DSA against quantum forgers, linear form.**

`qAdv^{EUF-CMA}(Q) + Pr[PRF ideal] + Pr[PRF_msg ideal] + Pr[SPprob] + (w−2)·Pr[UD ideal]
   ≤ Pr[PRF real] + Pr[PRF_msg real] + qAdv^{ITSR} + (Pr[DSPR] + 3·qAdv^{TCR}_F)
     + Σ_{n ∈ {1,2,len,k}} qAdv^{TCR}_{Thash|n} + (w−2)·Pr[UD real] + qAdv^{PRE}_F + qAdv^{TCR}_F`,

every probability a Born probability of an explicit quantum machine running `Q` once. -/
theorem slhdsa_euf_cma_final_linear_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q + qLinIdealEuf Q ≤ qLinRealEuf Q := by
  rw [qUnforgeableAdvantage_eq Q hQ, ← linIdealEuf_toClassical Q hQ,
    ← linRealEuf_toClassical Q hQ]
  exact slhdsa_euf_cma_final_linear' hS Q.toClassical

/-- **SUF-CMA of SLH-DSA against quantum forgers, linear form.** -/
theorem slhdsa_suf_cma_final_linear_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf Q ≤ qLinRealSuf Q := by
  rw [qStrongUnforgeableAdvantage_eq Q hQ, ← linIdealSuf_toClassical Q hQ,
    ← linRealSuf_toClassical Q hQ]
  exact slhdsa_suf_cma_final_linear' hS Q.toClassicalStrong

/-- **EUF-CMA of the external pure interface against quantum forgers, linear form**: the linear
bound at the internal quantum forger `qToInternal Q`. -/
theorem slhdsa_pure_euf_cma_final_linear_quantum (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qToInternal Q) ≤ qLinRealEuf (qToInternal Q) := by
  rw [qUnforgeableAdvantage_eq Q hQ,
    ← linIdealEuf_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    ← linRealEuf_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    toClassical_qToInternal]
  exact slhdsa_pure_euf_cma_final_linear hS Q.toClassical

/-- **SUF-CMA of the external pure interface against quantum forgers, linear form.** -/
theorem slhdsa_pure_suf_cma_final_linear_quantum (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qToInternal Q) ≤
      qLinRealSuf (qToInternal Q) := by
  rw [qStrongUnforgeableAdvantage_eq Q hQ,
    ← linIdealSuf_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    ← linRealSuf_toClassical (qToInternal Q) (rationalBorn_qToInternal Q hQ),
    toClassical_qToInternal]
  exact slhdsa_pure_suf_cma_final_linear hS Q.toClassicalStrong

end Reduction

#print axioms Reduction.qSM_DT_TCR_Advantage_qbTcrArM
#print axioms Reduction.slhdsa_euf_cma_final_memo_quantum
#print axioms Reduction.slhdsa_suf_cma_final_memo_quantum
#print axioms Reduction.slhdsa_pure_euf_cma_final_memo_quantum
#print axioms Reduction.slhdsa_pure_suf_cma_final_memo_quantum
#print axioms Reduction.slhdsa_euf_cma_final_linear_quantum
#print axioms Reduction.slhdsa_suf_cma_final_linear_quantum
#print axioms Reduction.slhdsa_pure_euf_cma_final_linear_quantum
#print axioms Reduction.slhdsa_pure_suf_cma_final_linear_quantum
