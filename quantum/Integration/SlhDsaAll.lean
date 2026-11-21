import PQ.Interactive.ApproxExtra
import Integration.SlhDsaApprox
import Integration.SlhDsaQuantumLinear
import Reduction.HeadlineFinal

/-!
# SLH-DSA against ALL quantum forgers: the final headlines, unconditionally

NOT part of the default target; checked by `scripts/check-integration.sh`.

Quantum versions, WITHOUT the hypothesis `RationalBorn`, of the final headlines of
`security/Reduction/HeadlineFinal.lean`, `TcrMemoHeadline.lean`, `Linear.lean`, `LinearBytes.lean`
(tight caps, memoising class adversaries `bTcrArM n`):

| scheme attacked by the quantum forger | EUF-CMA | SUF-CMA | linear EUF | linear SUF |
|---|---|---|---|---|
| `internalAlg` (typed, FIPS 205 internal) | `slhdsa_euf_cma_final_quantum_all` | `slhdsa_suf_cma_final_quantum_all` | `slhdsa_euf_cma_final_linear_quantum_all` | `slhdsa_suf_cma_final_linear_quantum_all` |
| `externalAlg` (typed, context strings) | `slhdsa_pure_euf_…` | `slhdsa_pure_suf_…` | `slhdsa_pure_euf_…_linear_…` | `slhdsa_pure_suf_…_linear_…` |
| `bytesAlg` (byte strings, internal) | `slhdsa_bytes_euf_…` | `slhdsa_bytes_suf_…` | `slhdsa_bytes_euf_…_linear_…` | `slhdsa_bytes_suf_…_linear_…` |
| `pureBytesAlg` (byte strings, context strings) | `slhdsa_pure_bytes_euf_…` | `slhdsa_pure_bytes_suf_…` | `slhdsa_pure_bytes_euf_…_linear_…` | `slhdsa_pure_bytes_suf_…_linear_…` |

They hold for EVERY quantum forger with classical signing queries (arbitrary amplitudes).  The
right-hand sides are `qBetaEufMemo` / `qBetaSufMemo` / `qLinIdeal…` / `qLinReal…` of
`Integration/SlhDsaQuantumLinear.lean`: every term is a Born probability or quantum advantage of
an explicit quantum machine that runs the forger once.  For the external and byte-level schemes
the forger is first wrapped in the classical interface translation (`qToInternal`,
`qBytesToTyped`, `qPureBytesToTyped`): classical code around the quantum machine.

These theorems supersede the `RationalBorn` versions (`…_memo_quantum`, `…_linear_quantum`,
`…_tight_quantum`), which are kept for reference.

Proof pattern (as in `Integration/SlhDsaApprox.lean`): for every sampler `s` each classical
reduction adversary applied to the classical approximant `Q.toClassicalWith s` is, as a program,
the `s`-approximant of the corresponding quantum machine; the classical quantities converge to the
quantum ones along the rational samplers `sampN`; the classical inequality passes to the limit.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive Topology
open Filter (Tendsto atTop)
open scoped ComplexOrder

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

-- as in `security/Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-! ## Program equalities for an arbitrary sampler: the machines of phase 2 -/

section programs

variable (s : Sampler W)

theorem toProbCompWith_qRunForgerSig {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    toProbCompWith s (qRunForgerSig Q pk sign) Q.ρ₀ = runForgerSig (Q.toClassicalWith s) pk sign :=
  toProbCompWith_wrap _ _ (forwardsUnifB_ofLift_add _) _ _ _

theorem toProbCompWith_qbPrfW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbPrfW w Q) Q.ρ₀ = bPrfW w (Q.toClassicalWith s) := by
  unfold qbPrfW
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerSig]
  rfl

theorem toProbCompWith_qbPrfWC (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbPrfWC w Q) Q.ρ₀ = bPrfWC w (Q.toClassicalWith s) := by
  rw [qbPrfWC, toProbCompWith_wrap0 _ _ (forwardsUnif0_restrictImpl _), toProbCompWith_qbPrfW]
  rfl

theorem toProbCompWith_qbPrfMsgWL (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbPrfMsgWL w Q) Q.ρ₀ = Lazy.bPrfMsgWL w (Q.toClassicalWith s) := by
  rw [qbPrfMsgWL, toProbCompWith_qLazyRun]
  unfold qMsgOpenW
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerSig]
  rfl

theorem toProbCompCWith_qMemoForge (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    toProbCompCWith s (qMemoForge n Q st pkSeed) Q.ρ₀ =
      (bTcrArM n (Q.toClassicalWith s)).forge st pkSeed := by
  rw [qMemoForge, toProbCompCWith_bind_liftU, toProbCompCWith_close _ _ (forwardsUnif_ofLift_add _),
    bTcrArM_forge]
  rfl

omit [Fintype prims.Y] in
/-- Abstract form: no concrete adversary is unfolded. -/
theorem toClassicalWith_qTcrOfClassical {ι PkSeed Tweak M Y : Type}
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (B B' : SM_DT_TCR_Adversary P)
    (qf : B.State → PkSeed → Closed W (ℕ × M)) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) (hS : B.State = B'.State) (hc : HEq B.choose B'.choose)
    (hf : HEq (fun st pk => toProbCompCWith s (qf st pk) ρ₀) B'.forge) :
    (qTcrOfClassical B qf ρ₀ h₁ h₂).toClassicalWith s = B' := by
  obtain ⟨S, c, f⟩ := B
  obtain ⟨S', c', f'⟩ := B'
  cases hS
  cases hc
  cases hf
  rfl

theorem bTcrArM_State_eq (n : ℕ) (A₁ A₂ : Forger vp prims optRand pkSeedDist) :
    (bTcrArM n A₁).State = (bTcrArM n A₂).State := rfl

/-- The `choose` phase of `bTcrArM n A` does not depend on the forger `A`. -/
theorem bTcrArM_choose_eq (n : ℕ) (A₁ A₂ : Forger vp prims optRand pkSeedDist) :
    (bTcrArM n A₁).choose = (bTcrArM n A₂).choose := rfl

/-- Generic in the two forgers (so that no unification problem compares two concrete forgers):
a quantum adversary built on the classical phases of `bTcrArM n A₁` whose quantum `forge` phase
`s`-classicalises to the `forge` phase of `bTcrArM n A₂` has `bTcrArM n A₂` as `s`-approximant. -/
theorem toClassicalWith_qTcrOfClassical_bTcrArM (n : ℕ)
    (A₁ A₂ : Forger vp prims optRand pkSeedDist)
    (qf : SecretTable vp prims × List (prims.AdrsKey × List prims.Y) → prims.PkSeed →
      Closed W (ℕ × {xs : List prims.Y // xs.length = n}))
    (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1)
    (h : ∀ st pk, toProbCompCWith s (qf st pk) ρ₀ = (bTcrArM n A₂).forge st pk) :
    (qTcrOfClassical (bTcrArM n A₁) qf ρ₀ h₁ h₂).toClassicalWith s = bTcrArM n A₂ :=
  toClassicalWith_qTcrOfClassical s (bTcrArM n A₁) (bTcrArM n A₂) qf ρ₀ h₁ h₂
    (bTcrArM_State_eq n A₁ A₂) (heq_of_eq (bTcrArM_choose_eq n A₁ A₂))
    (heq_of_eq (funext fun st => funext fun pk => h st pk))

theorem toClassicalWith_qbTcrArM (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qbTcrArM n Q).toClassicalWith s = bTcrArM n (Q.toClassicalWith s) :=
  toClassicalWith_qTcrOfClassical_bTcrArM s n _ _ _ _ _ _
    fun st pk => toProbCompCWith_qMemoForge s n Q st pk

theorem toClassicalWith_qrTcrT (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrTcrT Q).toClassicalWith s = rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s)) := by
  have hforge : ∀ (st : (SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
        List (WotsGame.Entry prims)) pk,
      ((qrTcrT Q).toClassicalWith s).forge st pk =
        (rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))).forge st pk := by
    intro st pk
    change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
    rfl
  change SM_DT_TCR_Adversary.mk _ _ _ = SM_DT_TCR_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hforge st pk

end programs

/-! ## The classical interface translations around a quantum forger -/

lemma forwardsUnif0_codedSigningImpl {M PK SK S PKb SKb Sb : Type}
    {alg : SignatureAlg ProbComp M PK SK S} {balg : SignatureAlg ProbComp M PKb SKb Sb}
    (v : Coded.View alg balg) : ForwardsUnif0 (Coded.signingImpl v) := fun _ ↦ rfl

/-- `Reduction.bytesToTyped` around a quantum forger against the byte-level internal scheme: the
public key is encoded, signing answers are encoded, the forged signature bytes are parsed —
classical code around the quantum machine.  A quantum forger against the typed internal scheme. -/
noncomputable def qBytesToTyped (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    QForger W (internalAlg vp prims optRand pkSeedDist) :=
  Q.wrapForger (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
    (bytesView vp prims codec optRand pkSeedDist).encPk
    (Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default))

theorem toClassicalWith_qBytesToTyped (s : Sampler W)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    (qBytesToTyped Q).toClassicalWith s = bytesToTyped (Q.toClassicalWith s) :=
  toClassicalWith_wrapForger s _ (forwardsUnif0_codedSigningImpl _) _ _ Q

/-- `Reduction.pureBytesToTyped` around a quantum forger against the byte-level external pure
scheme.  A quantum forger against the typed external scheme. -/
noncomputable def qPureBytesToTyped
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    QForger W (externalAlg vp prims optRand pkSeedDist) :=
  Q.wrapForger (Coded.signingImpl (pureBytesView vp prims codec optRand pkSeedDist))
    (pureBytesView vp prims codec optRand pkSeedDist).encPk
    (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
      (.error (.contextTooLong 0)))

theorem toClassicalWith_qPureBytesToTyped (s : Sampler W)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    (qPureBytesToTyped Q).toClassicalWith s = pureBytesToTyped (Q.toClassicalWith s) :=
  toClassicalWith_wrapForger s _ (forwardsUnif0_codedSigningImpl _) _ _ Q

theorem toClassicalWith_qToInternal (s : Sampler W)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    (qToInternal Q).toClassicalWith s = toInternal (Q.toClassicalWith s) := by
  have hmain : ∀ pk, ((qToInternal Q).toClassicalWith s).main pk =
      (toInternal (Q.toClassicalWith s)).main pk := by
    intro pk
    change toProbCompWith s (_ <$> wrap0 _ _) Q.ρ₀ = _
    rw [toProbCompWith_map, toProbCompWith_wrap0 _ _ (forwardsUnif0_signingImpl _)]
    rfl
  change SignatureAlg.UnforgeableAdversary.mk _ = SignatureAlg.UnforgeableAdversary.mk _
  congr 1
  funext pk
  exact hmain pk

/-! ## Limits of the terms -/

section limits

variable {samp : ℕ → Sampler W} (hs : BornApprox samp)
  (Q : QForger W (internalAlg vp prims optRand pkSeedDist))

include hs

theorem tendsto_tcr_bTcrArM (k : ℕ) :
    Tendsto (fun n ↦ SM_DT_TCR_Advantage (bTcrArM k (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qSM_DT_TCR_Advantage (qbTcrArM k Q))) := by
  simp only [← toClassicalWith_qbTcrArM]
  exact tendsto_SM_DT_TCR_Advantage hs _

theorem tendsto_tcr_rTcrT :
    Tendsto (fun n ↦ SM_DT_TCR_Advantage
        (rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qSM_DT_TCR_Advantage (qrTcrT Q))) := by
  simp only [← toClassicalWith_qrTcrT]
  exact tendsto_SM_DT_TCR_Advantage hs _

theorem tendsto_prfAdvantage_bPrfWC (w : WinCheck vp prims) :
    Tendsto (fun n ↦ (skPrfC vp prims).prfAdvantage (bPrfWC w (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qPrfAdvantage (skPrfC vp prims) (qbPrfWC w Q) Q.ρ₀)) := by
  simp only [← toProbCompWith_qbPrfWC]
  exact tendsto_prfAdvantage hs _ _ _ Q.posSemidef Q.trace_eq_one

theorem tendsto_prfAdvantage_bPrfMsgWL (w : WinCheck vp prims) :
    Tendsto (fun n ↦ (msgPrf vp prims).prfAdvantage
        (Lazy.bPrfMsgWL w (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgWL w Q) Q.ρ₀)) := by
  simp only [← toProbCompWith_qbPrfMsgWL]
  exact tendsto_prfAdvantage hs _ _ _ Q.posSemidef Q.trace_eq_one

/-- The memo bound at the approximants converges to the quantum memo bound (any PRF
distinguisher sequences whose advantages converge). -/
theorem tendsto_boundFinalMemo
    (B₁ : ℕ → PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : ℕ → MsgPrfAdv prims) {P₁ P₂ : ℝ≥0∞}
    (h₁ : Tendsto (fun n ↦ (skPrfC vp prims).prfAdvantage (B₁ n)) atTop (𝓝 P₁))
    (h₂ : Tendsto (fun n ↦ (msgPrf vp prims).prfAdvantage (B₂ n)) atTop (𝓝 P₂)) :
    Tendsto (fun n ↦ boundFinalTight pkSeedDist (B₁ n) (B₂ n)
        (Lazy.bItsrL (Q.toClassicalWith (samp n)))
        (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (toTcr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (bTcrArM 1 (Q.toClassicalWith (samp n))) (bTcrArM 2 (Q.toClassicalWith (samp n)))
        (bTcrArM vp.params.len (Q.toClassicalWith (samp n)))
        (bTcrArM vp.params.k (Q.toClassicalWith (samp n)))
        (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))
        (rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))
        (rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qBoundMemo Q P₁ P₂)) := by
  unfold boundFinalTight qBoundMemo
  have hC := (((tendsto_tcr_bTcrArM hs Q 1).add (tendsto_tcr_bTcrArM hs Q 2)).add
    (tendsto_tcr_bTcrArM hs Q vp.params.len)).add (tendsto_tcr_bTcrArM hs Q vp.params.k)
  have hF := (tendsto_dspr_toDspr hs Q).add
    (ENNReal.Tendsto.const_mul (a := (3 : ℝ≥0∞)) (tendsto_tcr_toTcr hs Q) (Or.inr (by simp)))
  have hU := ENNReal.Tendsto.const_mul (a := ((vp.params.w - 2 : ℕ) : ℝ≥0∞))
    (tendsto_ud_rUd hs Q) (Or.inr (ENNReal.natCast_ne_top _))
  exact ((((((h₁.add h₂).add (tendsto_itsrAdvantage_bItsrL hs Q)).add hF).add hC).add hU).add
    (tendsto_pre_rPre hs Q)).add (tendsto_tcr_rTcrT hs Q)

theorem tendsto_betaEufFinalMemo :
    Tendsto (fun n ↦ betaEufFinalMemo (Q.toClassicalWith (samp n))) atTop
      (𝓝 (qBetaEufMemo Q)) :=
  tendsto_boundFinalMemo hs Q _ _ (tendsto_prfAdvantage_bPrfC hs Q)
    (tendsto_prfAdvantage_bPrfMsgL hs Q)

theorem tendsto_betaSufFinalMemo :
    Tendsto (fun n ↦ betaSufFinalMemo (Q.toClassicalWith (samp n))) atTop
      (𝓝 (qBetaSufMemo Q)) :=
  tendsto_boundFinalMemo hs Q _ _ (tendsto_prfAdvantage_bPrfWC hs Q sufCheck)
    (tendsto_prfAdvantage_bPrfMsgWL hs Q sufCheck)

/-! ### The two sides of the linear form -/

theorem tendsto_linearIdealSide
    (B₁ : ℕ → PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : ℕ → MsgPrfAdv prims) {I₁ I₂ : ℝ≥0∞}
    (h₁ : Tendsto (fun n ↦ prfIdealPr (B₁ n)) atTop (𝓝 I₁))
    (h₂ : Tendsto (fun n ↦ msgIdealPr (B₂ n)) atTop (𝓝 I₂)) :
    Tendsto (fun n ↦ linearIdealSide (B₁ n) (B₂ n)
        (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qLinearIdealSide Q I₁ I₂)) := by
  unfold linearIdealSide qLinearIdealSide
  have hD : Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.SPProbability
      (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qDsprFV_SPProbability (qToDspr Q))) := by
    simp only [← toClassicalWith_qToDspr]
    exact tendsto_qDsprFV_SPProbability hs _
  have hU : Tendsto (fun n ↦ SM_DT_UD_IdealSuccess
      (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qSM_DT_UD_IdealSuccess (qrUd Q))) := by
    simp only [← toClassicalWith_qrUd]
    exact tendsto_qSM_DT_UD_IdealSuccess hs _
  exact ((h₁.add h₂).add hD).add
    (ENNReal.Tendsto.const_mul hU (Or.inr (ENNReal.natCast_ne_top _)))

theorem tendsto_linearRealSide
    (B₁ : ℕ → PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : ℕ → MsgPrfAdv prims) {R₁ R₂ : ℝ≥0∞}
    (h₁ : Tendsto (fun n ↦ prfRealPr (B₁ n)) atTop (𝓝 R₁))
    (h₂ : Tendsto (fun n ↦ msgRealPr (B₂ n)) atTop (𝓝 R₂)) :
    Tendsto (fun n ↦ linearRealSide pkSeedDist (B₁ n) (B₂ n)
        (Lazy.bItsrL (Q.toClassicalWith (samp n)))
        (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (toTcr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (bTcrArM 1 (Q.toClassicalWith (samp n))) (bTcrArM 2 (Q.toClassicalWith (samp n)))
        (bTcrArM vp.params.len (Q.toClassicalWith (samp n)))
        (bTcrArM vp.params.k (Q.toClassicalWith (samp n)))
        (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))
        (rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))
        (rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qLinearRealSide Q R₁ R₂)) := by
  unfold linearRealSide qLinearRealSide
  have hD : Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.Success
      (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qDsprFV_Success (qToDspr Q))) := by
    simp only [← toClassicalWith_qToDspr]
    exact tendsto_qDsprFV_Success hs _
  have hU : Tendsto (fun n ↦ SM_DT_UD_RealSuccess
      (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qSM_DT_UD_RealSuccess (qrUd Q))) := by
    simp only [← toClassicalWith_qrUd]
    exact tendsto_qSM_DT_UD_RealSuccess hs _
  have hC := (((tendsto_tcr_bTcrArM hs Q 1).add (tendsto_tcr_bTcrArM hs Q 2)).add
    (tendsto_tcr_bTcrArM hs Q vp.params.len)).add (tendsto_tcr_bTcrArM hs Q vp.params.k)
  have hF := hD.add
    (ENNReal.Tendsto.const_mul (a := (3 : ℝ≥0∞)) (tendsto_tcr_toTcr hs Q) (Or.inr (by simp)))
  have hU' := ENNReal.Tendsto.const_mul (a := ((vp.params.w - 2 : ℕ) : ℝ≥0∞))
    hU (Or.inr (ENNReal.natCast_ne_top _))
  exact ((((((h₁.add h₂).add (tendsto_itsrAdvantage_bItsrL hs Q)).add hF).add hC).add hU').add
    (tendsto_pre_rPre hs Q)).add (tendsto_tcr_rTcrT hs Q)

theorem tendsto_linIdealEuf :
    Tendsto (fun n ↦ linIdealEuf (Q.toClassicalWith (samp n))) atTop (𝓝 (qLinIdealEuf Q)) := by
  refine tendsto_linearIdealSide hs Q _ _ ?_ ?_
  · simp only [prfIdealPr, ← toProbCompWith_qbPrfC]
    exact tendsto_qPrfIdealPr hs _ _ Q.posSemidef Q.trace_eq_one
  · simp only [msgIdealPr, ← toProbCompWith_qbPrfMsgL]
    exact tendsto_qPrfIdealPr hs _ _ Q.posSemidef Q.trace_eq_one

theorem tendsto_linRealEuf :
    Tendsto (fun n ↦ linRealEuf (Q.toClassicalWith (samp n))) atTop (𝓝 (qLinRealEuf Q)) := by
  refine tendsto_linearRealSide hs Q _ _ ?_ ?_
  · simp only [prfRealPr, ← toProbCompWith_qbPrfC]
    exact tendsto_qPrfRealPr hs _ _ _ Q.posSemidef Q.trace_eq_one
  · simp only [msgRealPr, ← toProbCompWith_qbPrfMsgL]
    exact tendsto_qPrfRealPr hs _ _ _ Q.posSemidef Q.trace_eq_one

theorem tendsto_linIdealSuf :
    Tendsto (fun n ↦ linIdealSuf (Q.toClassicalWith (samp n))) atTop (𝓝 (qLinIdealSuf Q)) := by
  refine tendsto_linearIdealSide hs Q _ _ ?_ ?_
  · simp only [prfIdealPr, ← toProbCompWith_qbPrfWC]
    exact tendsto_qPrfIdealPr hs _ _ Q.posSemidef Q.trace_eq_one
  · simp only [msgIdealPr, ← toProbCompWith_qbPrfMsgWL]
    exact tendsto_qPrfIdealPr hs _ _ Q.posSemidef Q.trace_eq_one

theorem tendsto_linRealSuf :
    Tendsto (fun n ↦ linRealSuf (Q.toClassicalWith (samp n))) atTop (𝓝 (qLinRealSuf Q)) := by
  refine tendsto_linearRealSide hs Q _ _ ?_ ?_
  · simp only [prfRealPr, ← toProbCompWith_qbPrfWC]
    exact tendsto_qPrfRealPr hs _ _ _ Q.posSemidef Q.trace_eq_one
  · simp only [msgRealPr, ← toProbCompWith_qbPrfMsgWL]
    exact tendsto_qPrfRealPr hs _ _ _ Q.posSemidef Q.trace_eq_one

end limits

/-! ## The lifting lemmas -/

section lifting

variable {Mb PKb SKb Sb : Type} {balg : SignatureAlg ProbComp Mb PKb SKb Sb}

/-- EUF-CMA: a classical bound `Adv(A) ≤ betaEufFinalMemo (T A)` for all classical forgers
against `balg`, where the classical translation `T` commutes with classicalisation of the quantum
forger `Q` into the internal quantum forger `qT`, gives the quantum bound. -/
theorem euf_memo_all (Q : QForger W balg)
    (T : SignatureAlg.UnforgeableAdversary balg → Forger vp prims optRand pkSeedDist)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hT : ∀ s, qT.toClassicalWith s = T (Q.toClassicalWith s))
    (h : ∀ A, SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (T A)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo qT := by
  refine le_of_forall_classical_of_tendsto
    (f := fun A ↦ SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A)
    (g := fun A ↦ betaEufFinalMemo (T A)) h (fun n ↦ Q.toClassicalWith (sampN n))
    (tendsto_unforgeableAdvantage bornApprox_sampN Q) ?_
  simp only [← hT]
  exact tendsto_betaEufFinalMemo bornApprox_sampN qT

theorem suf_memo_all (Q : QForger W balg)
    (T : SignatureAlg.UnforgeableAdversary balg → Forger vp prims optRand pkSeedDist)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hT : ∀ s, qT.toClassicalWith s = T (Q.toClassicalWith s))
    (h : ∀ S : SignatureAlg.StrongUnforgeableAdversary balg,
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalMemo (T S.toUnforgeableAdversary)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo qT := by
  refine le_of_forall_classical_of_tendsto
    (f := fun S ↦ SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S)
    (g := fun S ↦ betaSufFinalMemo (T S.toUnforgeableAdversary)) h
    (fun n ↦ Q.toClassicalStrongWith (sampN n))
    (tendsto_strongUnforgeableAdvantage bornApprox_sampN Q) ?_
  have e : ∀ n, (Q.toClassicalStrongWith (sampN n)).toUnforgeableAdversary =
      Q.toClassicalWith (sampN n) := fun _ ↦ rfl
  simp only [e, ← hT]
  exact tendsto_betaSufFinalMemo bornApprox_sampN qT

theorem euf_linear_all (Q : QForger W balg)
    (T : SignatureAlg.UnforgeableAdversary balg → Forger vp prims optRand pkSeedDist)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hT : ∀ s, qT.toClassicalWith s = T (Q.toClassicalWith s))
    (h : ∀ A, SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (T A) ≤
      linRealEuf (T A)) :
    qUnforgeableAdvantage Q + qLinIdealEuf qT ≤ qLinRealEuf qT := by
  refine le_of_forall_classical_of_tendsto
    (f := fun A ↦ SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
      linIdealEuf (T A))
    (g := fun A ↦ linRealEuf (T A)) h (fun n ↦ Q.toClassicalWith (sampN n)) ?_ ?_
  · simp only [← hT]
    exact (tendsto_unforgeableAdvantage bornApprox_sampN Q).add
      (tendsto_linIdealEuf bornApprox_sampN qT)
  · simp only [← hT]
    exact tendsto_linRealEuf bornApprox_sampN qT

theorem suf_linear_all (Q : QForger W balg)
    (T : SignatureAlg.UnforgeableAdversary balg → Forger vp prims optRand pkSeedDist)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hT : ∀ s, qT.toClassicalWith s = T (Q.toClassicalWith s))
    (h : ∀ S : SignatureAlg.StrongUnforgeableAdversary balg,
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (T S.toUnforgeableAdversary) ≤ linRealSuf (T S.toUnforgeableAdversary)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf qT ≤ qLinRealSuf qT := by
  have e : ∀ n, (Q.toClassicalStrongWith (sampN n)).toUnforgeableAdversary =
      Q.toClassicalWith (sampN n) := fun _ ↦ rfl
  refine le_of_forall_classical_of_tendsto
    (f := fun S ↦ SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
      linIdealSuf (T S.toUnforgeableAdversary))
    (g := fun S ↦ linRealSuf (T S.toUnforgeableAdversary)) h
    (fun n ↦ Q.toClassicalStrongWith (sampN n)) ?_ ?_
  · simp only [e, ← hT]
    exact (tendsto_strongUnforgeableAdvantage bornApprox_sampN Q).add
      (tendsto_linIdealSuf bornApprox_sampN qT)
  · simp only [e, ← hT]
    exact tendsto_linRealSuf bornApprox_sampN qT

end lifting

/-! ## Headlines: the typed internal scheme -/

/-- **EUF-CMA of SLH-DSA (internal algorithms) against every quantum forger.**  No hypothesis on
the forger.  Supersedes `slhdsa_euf_cma_final_memo_quantum`. -/
theorem slhdsa_euf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo Q :=
  euf_memo_all Q id Q (fun _ ↦ rfl) (slhdsa_euf_cma_final_memo' hS)

/-- **SUF-CMA of SLH-DSA (internal algorithms) against every quantum forger.** -/
theorem slhdsa_suf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo Q :=
  suf_memo_all Q id Q (fun _ ↦ rfl) (slhdsa_suf_cma_final_memo' hS)

/-- **EUF-CMA of SLH-DSA (internal algorithms) against every quantum forger, linear form.** -/
theorem slhdsa_euf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf Q ≤ qLinRealEuf Q :=
  euf_linear_all Q id Q (fun _ ↦ rfl) (slhdsa_euf_cma_final_linear' hS)

/-- **SUF-CMA of SLH-DSA (internal algorithms) against every quantum forger, linear form.** -/
theorem slhdsa_suf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf Q ≤ qLinRealSuf Q :=
  suf_linear_all Q id Q (fun _ ↦ rfl) (slhdsa_suf_cma_final_linear' hS)

/-! ## Headlines: the typed external pure interface -/

/-- **EUF-CMA of the external pure interface against every quantum forger.** -/
theorem slhdsa_pure_euf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qToInternal Q) :=
  euf_memo_all Q toInternal (qToInternal Q) (fun s ↦ toClassicalWith_qToInternal s Q)
    (slhdsa_pure_euf_cma_final_memo' hS)

/-- **SUF-CMA of the external pure interface against every quantum forger.** -/
theorem slhdsa_pure_suf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qToInternal Q) :=
  suf_memo_all Q toInternal (qToInternal Q) (fun s ↦ toClassicalWith_qToInternal s Q)
    (slhdsa_pure_suf_cma_final_memo' hS)

theorem slhdsa_pure_euf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qToInternal Q) ≤ qLinRealEuf (qToInternal Q) :=
  euf_linear_all Q toInternal (qToInternal Q) (fun s ↦ toClassicalWith_qToInternal s Q)
    (fun A ↦ slhdsa_pure_euf_cma_final_linear hS A)

theorem slhdsa_pure_suf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qToInternal Q) ≤ qLinRealSuf (qToInternal Q) :=
  suf_linear_all Q toInternal (qToInternal Q) (fun s ↦ toClassicalWith_qToInternal s Q)
    (fun S ↦ slhdsa_pure_suf_cma_final_linear hS S)

/-! ## Headlines: byte strings, internal interface -/

/-- **EUF-CMA of SLH-DSA on byte strings against every quantum forger — final form.**  For every
quantum forger `Q` against `bytesAlg` (public key, messages and signatures are byte strings;
classical signing queries), the quantum EUF-CMA advantage is at most the twelve quantum advantages
of `qBetaEufMemo` at the typed quantum forger `qBytesToTyped Q`. -/
theorem slhdsa_bytes_euf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qBytesToTyped Q) :=
  euf_memo_all Q bytesToTyped (qBytesToTyped Q) (fun s ↦ toClassicalWith_qBytesToTyped s Q)
    (fun A ↦ slhdsa_bytes_euf_cma_final hS A)

/-- **SUF-CMA of SLH-DSA on byte strings against every quantum forger — final form.** -/
theorem slhdsa_bytes_suf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qBytesToTyped Q) :=
  suf_memo_all Q bytesToTyped (qBytesToTyped Q) (fun s ↦ toClassicalWith_qBytesToTyped s Q)
    (fun S ↦ slhdsa_bytes_suf_cma_final hS S)

theorem slhdsa_bytes_euf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qBytesToTyped Q) ≤ qLinRealEuf (qBytesToTyped Q) :=
  euf_linear_all Q bytesToTyped (qBytesToTyped Q) (fun s ↦ toClassicalWith_qBytesToTyped s Q)
    (fun A ↦ slhdsa_bytes_euf_cma_linear hS A)

theorem slhdsa_bytes_suf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qBytesToTyped Q) ≤
      qLinRealSuf (qBytesToTyped Q) :=
  suf_linear_all Q bytesToTyped (qBytesToTyped Q) (fun s ↦ toClassicalWith_qBytesToTyped s Q)
    (fun S ↦ slhdsa_bytes_suf_cma_linear hS S)

/-! ## Headlines: byte strings, external pure interface -/

/-- The internal typed quantum forger obtained from a quantum forger against the byte-level
external pure scheme: `toInternal ∘ pureBytesToTyped` around the quantum machine. -/
noncomputable def qPureBytesToInternal
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    QForger W (internalAlg vp prims optRand pkSeedDist) :=
  qToInternal (qPureBytesToTyped Q)

theorem toClassicalWith_qPureBytesToInternal (s : Sampler W)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    (qPureBytesToInternal Q).toClassicalWith s =
      toInternal (pureBytesToTyped (Q.toClassicalWith s)) := by
  rw [qPureBytesToInternal, toClassicalWith_qToInternal, toClassicalWith_qPureBytesToTyped]

/-- **EUF-CMA of the external pure interface on byte strings against every quantum forger —
final form.** -/
theorem slhdsa_pure_bytes_euf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qPureBytesToInternal Q) :=
  euf_memo_all Q (fun A ↦ toInternal (pureBytesToTyped A)) (qPureBytesToInternal Q)
    (fun s ↦ toClassicalWith_qPureBytesToInternal s Q)
    (fun A ↦ slhdsa_pure_bytes_euf_cma_final hS A)

/-- **SUF-CMA of the external pure interface on byte strings against every quantum forger —
final form.** -/
theorem slhdsa_pure_bytes_suf_cma_final_quantum_all (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qPureBytesToInternal Q) :=
  suf_memo_all Q (fun A ↦ toInternal (pureBytesToTyped A)) (qPureBytesToInternal Q)
    (fun s ↦ toClassicalWith_qPureBytesToInternal s Q)
    (fun S ↦ slhdsa_pure_bytes_suf_cma_final hS S)

theorem slhdsa_pure_bytes_euf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qPureBytesToInternal Q) ≤
      qLinRealEuf (qPureBytesToInternal Q) :=
  euf_linear_all Q (fun A ↦ toInternal (pureBytesToTyped A)) (qPureBytesToInternal Q)
    (fun s ↦ toClassicalWith_qPureBytesToInternal s Q)
    (fun A ↦ slhdsa_pure_bytes_euf_cma_linear hS A)

theorem slhdsa_pure_bytes_suf_cma_final_linear_quantum_all (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qPureBytesToInternal Q) ≤
      qLinRealSuf (qPureBytesToInternal Q) :=
  suf_linear_all Q (fun A ↦ toInternal (pureBytesToTyped A)) (qPureBytesToInternal Q)
    (fun s ↦ toClassicalWith_qPureBytesToInternal s Q)
    (fun S ↦ slhdsa_pure_bytes_suf_cma_linear hS S)

end Reduction

#print axioms Reduction.toClassicalWith_qbTcrArM
#print axioms Reduction.toClassicalWith_qrTcrT
#print axioms Reduction.toClassicalWith_qBytesToTyped
#print axioms Reduction.slhdsa_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_suf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_pure_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_pure_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_pure_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_pure_suf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_bytes_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_bytes_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_bytes_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_bytes_suf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_pure_bytes_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_pure_bytes_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_pure_bytes_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_pure_bytes_suf_cma_final_linear_quantum_all
