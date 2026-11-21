import PQ.Interactive.ApproxGames
import Integration.SlhDsaQuantum

/-!
# SLH-DSA against quantum forgers with ARBITRARY amplitudes (integration)

NOT part of the default target.  This file imports `Integration.SlhDsaQuantum` (which is not built
by lake) and the compiled `Reduction.Headline` of `security/` (read-only).  Check it with

```
cd quantum
LP="$(lake env printenv LEAN_PATH):$PWD/../security/.lake/build/lib/lean:\
$PWD/../.tools/aeneas/backends/lean/.lake/build/lib/lean"
mkdir -p /tmp/slhq/Integration
LEAN_PATH="$LP" lean -o /tmp/slhq/Integration/SlhDsaQuantum.olean Integration/SlhDsaQuantum.lean
LEAN_PATH="$LP:/tmp/slhq" lean Integration/SlhDsaApprox.lean
```

`slhdsa_euf_cma_final_quantum_machines_all` is `slhdsa_euf_cma_final_quantum_machines` (same
statement, same nine quantum machines, same quantum advantages) WITHOUT the hypothesis
`RationalBorn`: it holds for every quantum forger with classical signing queries.

Proof: the classical theorem `slhdsa_euf_cma_final'` is applied to the classical approximants
`Q.toClassicalN n` of the forger (rational samplers `sampN n`).  Each of the nine reduction
adversaries applied to the approximant is, as a program, the `n`-th approximant of the
corresponding quantum machine (the syntactic commutation lemmas hold for every sampler), so both
sides of the classical inequality converge to the quantum quantities (`ApproxGames.lean`), and the
inequality passes to the limit.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive Topology
open Filter (Tendsto atTop)

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

/-! ## Program equalities for an arbitrary sampler (L4) -/

section programs

variable (s : Sampler W)

theorem toProbCompWith_qbPrf (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbPrf Q) Q.ρ₀ = bPrf (Q.toClassicalWith s) := by
  unfold qbPrf
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForger]
  rfl

theorem toProbCompWith_qbPrfC (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbPrfC Q) Q.ρ₀ = bPrfC (Q.toClassicalWith s) := by
  rw [qbPrfC, toProbCompWith_wrap0 _ _ (forwardsUnif0_restrictImpl _), toProbCompWith_qbPrf]
  rfl

section lazy

open Lazy

variable {ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ} {D V α : Type}

theorem toProbCompWith_qLazyRun [DecidableEq D] [SampleableType V] (hI : QueryImpl hspec Id)
    (X : QOC W (RSpec gspec D V hspec) α) (ρ : Matrix W W ℂ) :
    toProbCompWith s (qLazyRun hI X) ρ = lazyRun hI (toProbCompWith s X ρ) := by
  rw [qLazyRun, toProbCompWith_wrap0 _ _ (forwardsUnif0_interp hI), toProbCompWith_map,
    toProbCompWith_wrap _ _ forwardsUnifB_lazyImplR]
  rfl

theorem toProbCompWith_qbPrfMsgL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbPrfMsgL Q) Q.ρ₀ = bPrfMsgL (Q.toClassicalWith s) := by
  rw [qbPrfMsgL, toProbCompWith_qLazyRun]
  unfold qMsgOpen
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForger]
  rfl

theorem toProbCompWith_qRunForgerLog {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    toProbCompWith s (qRunForgerLog Q pk randomizer signR) Q.ρ₀ =
      runForgerLog (Q.toClassicalWith s) pk randomizer signR :=
  toProbCompWith_wrap _ _ (forwardsUnifB_ofLift_add _) _ _ _

theorem toProbCompWith_qbItsrL (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    toProbCompWith s (qbItsrL Q) Q.ρ₀ = (bItsrL (Q.toClassicalWith s)).main := by
  rw [qbItsrL, toProbCompWith_qLazyRun]
  unfold qItsrOpen
  simp only [toProbCompWith_liftQ_bind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerLog]
  rfl

end lazy

theorem toClassicalWith_qbTcrS (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qbTcrS Q).toClassicalWith s = Lazy.bTcrS (Q.toClassicalWith s) := by
  have hforge : ∀ tbl pkSeed, ((qbTcrS Q).toClassicalWith s).forge tbl pkSeed =
      (Lazy.bTcrS (Q.toClassicalWith s)).forge tbl pkSeed := by
    intro tbl pkSeed
    change toProbCompCWith s (_ >>= fun r => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_close _ _ (forwardsUnif_ofLift_add _)]
    rfl
  change TweakableHash.SM_DT_TCR_Adversary.mk _ _ _ = TweakableHash.SM_DT_TCR_Adversary.mk _ _ _
  congr 1
  funext tbl pkSeed
  exact hforge tbl pkSeed

theorem toProbCompCWith_qWotsForge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed) :
    toProbCompCWith s (qWotsForge Q st pkSeed) Q.ρ₀ =
      (Lazy.bWotsS (Q.toClassicalWith s)).forge st pkSeed := by
  rw [qWotsForge, toProbCompCWith_bind_liftU, toProbCompCWith_close _ _ (forwardsUnif_ofLift_add _)]
  rfl

theorem toClassicalWith_qrTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrTcr Q).toClassicalWith s = rTcr pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s)) := by
  have hforge : ∀ st pk, ((qrTcr Q).toClassicalWith s).forge st pk =
      (rTcr pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))).forge st pk := by
    intro st pk
    change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
    rfl
  change TweakableHash.SM_DT_TCR_Adversary.mk _ _ _ = TweakableHash.SM_DT_TCR_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hforge st pk

theorem toClassicalWith_qrPre (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrPre Q).toClassicalWith s = rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s)) := by
  have hinv : ∀ st pk, ((qrPre Q).toClassicalWith s).invert st pk =
      (rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))).invert st pk := by
    intro st pk
    change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
    rfl
  change TweakableHash.SM_DT_PRE_Adversary.mk _ _ _ = TweakableHash.SM_DT_PRE_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hinv st pk

theorem toClassicalWith_qrUd (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qrUd Q).toClassicalWith s = rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s)) := by
  have hd : ∀ st pk, ((qrUd Q).toClassicalWith s).distinguish st pk =
      (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith s))).distinguish st pk := by
    intro st pk
    change toProbCompCWith s (_ >>= fun x => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_qWotsForge]
    rfl
  change TweakableHash.SM_DT_UD_Adversary.mk _ _ _ = TweakableHash.SM_DT_UD_Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hd st pk

theorem toProbCompWith_qOpenPreFind (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    toProbCompWith s (qOpenPreFind Q tbl pkSeed ys) Q.ρ₀ =
      (Lazy.bOpenPreS (Q.toClassicalWith s)).find tbl pkSeed ys := by
  rw [qOpenPreFind, toProbCompWith_bind_liftQ, toProbCompWith_qRunForgerLog]
  rfl

open TweakableHash in
theorem toProbCompCWith_qFindRun (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) :
    toProbCompCWith s (qFindRun Q st pkSeed) Q.ρ₀ =
      (simulateQ (SM_DT_OpenPRE_SourceFinalValidity.findOracles st.2.1)
        ((Lazy.bOpenPreS (Q.toClassicalWith s)).find st.1 pkSeed st.2.2)).run [] := by
  have hf : ForwardsUnif (SM_DT_OpenPRE_SourceFinalValidity.findOracles (M := prims.Y) st.2.1) :=
    forwardsUnif_ofLift_add _
  rw [qFindRun, toProbCompCWith_close _ _ hf, toProbCompWith_qOpenPreFind]

theorem toClassicalWith_qToTcr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qToTcr Q).toClassicalWith s = toTcr (Lazy.bOpenPreS (Q.toClassicalWith s)) := by
  have hforge : ∀ (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y) pk,
      ((qToTcr Q).toClassicalWith s).forge st pk =
        (toTcr (Lazy.bOpenPreS (Q.toClassicalWith s))).forge st pk := by
    intro st pk
    change toProbCompCWith s (_ >>= fun r => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_qFindRun]
    rfl
  change TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary.mk _ _ _ =
    TweakableHash.SM_DT_TCR_SourceFinalValidity.Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hforge st pk

theorem toClassicalWith_qToDspr (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qToDspr Q).toClassicalWith s = toDspr (Lazy.bOpenPreS (Q.toClassicalWith s)) := by
  have hguess : ∀ (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y) pk,
      ((qToDspr Q).toClassicalWith s).guess st pk =
        (toDspr (Lazy.bOpenPreS (Q.toClassicalWith s))).guess st pk := by
    intro st pk
    change toProbCompCWith s (_ >>= fun r => liftU _) Q.ρ₀ = _
    rw [toProbCompCWith_bind_liftU, toProbCompCWith_qFindRun]
    rfl
  change TweakableHash.SM_DT_DSPR_SourceFinalValidity.Adversary.mk _ _ _ =
    TweakableHash.SM_DT_DSPR_SourceFinalValidity.Adversary.mk _ _ _
  congr 1
  funext st pk
  exact hguess st pk

end programs

/-! ## The nine terms of the bound as limits -/

section limits

variable {samp : ℕ → Sampler W} (hs : BornApprox samp)
  (Q : QForger W (internalAlg vp prims optRand pkSeedDist))

include hs

theorem tendsto_prfAdvantage_bPrfC :
    Tendsto (fun n ↦ (skPrfC vp prims).prfAdvantage (bPrfC (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀)) := by
  simp only [← toProbCompWith_qbPrfC]
  exact tendsto_prfAdvantage hs _ _ _ Q.posSemidef Q.trace_eq_one

theorem tendsto_prfAdvantage_bPrfMsgL :
    Tendsto (fun n ↦ (msgPrf vp prims).prfAdvantage (Lazy.bPrfMsgL (Q.toClassicalWith (samp n))))
      atTop (𝓝 (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀)) := by
  simp only [← toProbCompWith_qbPrfMsgL]
  exact tendsto_prfAdvantage hs _ _ _ Q.posSemidef Q.trace_eq_one

theorem tendsto_itsrAdvantage_bItsrL :
    Tendsto (fun n ↦ KeyedHash.ITSRAdvantage (Lazy.bItsrL (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀)) := by
  refine (tendsto_itsrAdvantage hs (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ Q.posSemidef
    Q.trace_eq_one).congr fun n ↦ ?_
  rw [toProbCompWith_qbItsrL]

theorem tendsto_dspr_toDspr :
    Tendsto (fun n ↦ TweakableHash.SM_DT_DSPR_SourceFinalValidity.advantage
        (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qDsprFV_Advantage (qToDspr Q))) := by
  simp only [← toClassicalWith_qToDspr]
  exact tendsto_dsprFV_advantage hs _

theorem tendsto_tcr_toTcr :
    Tendsto (fun n ↦ TweakableHash.SM_DT_TCR_SourceFinalValidity.advantage
        (toTcr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qTcrFV_Advantage (qToTcr Q))) := by
  simp only [← toClassicalWith_qToTcr]
  exact tendsto_tcrFV_advantage hs _

theorem tendsto_tcr_bTcrS :
    Tendsto (fun n ↦ TweakableHash.SM_DT_TCR_Advantage
        (Lazy.bTcrS (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qSM_DT_TCR_Advantage (qbTcrS Q))) := by
  simp only [← toClassicalWith_qbTcrS]
  exact tendsto_SM_DT_TCR_Advantage hs _

theorem tendsto_ud_rUd :
    Tendsto (fun n ↦ TweakableHash.SM_DT_UD_Advantage
        (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qSM_DT_UD_Advantage (qrUd Q))) := by
  simp only [← toClassicalWith_qrUd]
  exact tendsto_SM_DT_UD_Advantage hs _

theorem tendsto_pre_rPre :
    Tendsto (fun n ↦ TweakableHash.SM_DT_PRE_Advantage
        (rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qSM_DT_PRE_Advantage (qrPre Q))) := by
  simp only [← toClassicalWith_qrPre]
  exact tendsto_SM_DT_PRE_Advantage hs _

theorem tendsto_tcr_rTcr :
    Tendsto (fun n ↦ TweakableHash.SM_DT_TCR_Advantage
        (rTcr pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qSM_DT_TCR_Advantage (qrTcr Q))) := by
  simp only [← toClassicalWith_qrTcr]
  exact tendsto_SM_DT_TCR_Advantage hs _

/-- The classical bound `betaEufFinal` at the classical approximants of the quantum forger
converges to the bound with the nine quantum advantages. -/
theorem tendsto_betaEufFinal :
    Tendsto (fun n ↦ betaEufFinal (Q.toClassicalWith (samp n))) atTop
      (𝓝 (qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀ +
        qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀ +
        qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
        (qDsprFV_Advantage (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
        qSM_DT_TCR_Advantage (qbTcrS Q) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_Advantage (qrUd Q) +
        qSM_DT_PRE_Advantage (qrPre Q) +
        qSM_DT_TCR_Advantage (qrTcr Q))) := by
  unfold betaEufFinal boundFinal
  exact (((((((tendsto_prfAdvantage_bPrfC hs Q).add (tendsto_prfAdvantage_bPrfMsgL hs Q)).add
    (tendsto_itsrAdvantage_bItsrL hs Q)).add
    ((tendsto_dspr_toDspr hs Q).add
      (ENNReal.Tendsto.const_mul (tendsto_tcr_toTcr hs Q) (Or.inr (by simp))))).add
    (tendsto_tcr_bTcrS hs Q)).add
    (ENNReal.Tendsto.const_mul (tendsto_ud_rUd hs Q) (Or.inr (ENNReal.natCast_ne_top _)))).add
    (tendsto_pre_rPre hs Q)).add (tendsto_tcr_rTcr hs Q)

end limits

/-! ## The unconditional theorem -/

/-- **Standard-model EUF-CMA security of SLH-DSA against quantum forgers with arbitrary
amplitudes, with every reduction adversary a quantum machine.**  This is
`slhdsa_euf_cma_final_quantum_machines` without the hypothesis `RationalBorn`: for EVERY quantum
forger `Q` with classical signing queries, the quantum EUF-CMA advantage is bounded by the nine
terms of `Reduction.boundFinal`, each of them the quantum advantage (Born probabilities,
`qWeight`) of the explicit quantum machine that runs `Q` once inside the classical code of the
corresponding reduction adversary. -/
theorem slhdsa_euf_cma_final_quantum_machines_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤
      qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀ +
        qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀ +
        qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
        (qDsprFV_Advantage (qToDspr Q) + 3 * qTcrFV_Advantage (qToTcr Q)) +
        qSM_DT_TCR_Advantage (qbTcrS Q) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_Advantage (qrUd Q) +
        qSM_DT_PRE_Advantage (qrPre Q) +
        qSM_DT_TCR_Advantage (qrTcr Q) :=
  qUnforgeableAdvantage_le_of_forall_of_tendsto Q betaEufFinal (slhdsa_euf_cma_final' hS)
    (tendsto_betaEufFinal bornApprox_sampN Q)

end Reduction

#print axioms Reduction.toProbCompWith_qbPrfC
#print axioms Reduction.toProbCompWith_qbPrfMsgL
#print axioms Reduction.toProbCompWith_qbItsrL
#print axioms Reduction.toClassicalWith_qbTcrS
#print axioms Reduction.toClassicalWith_qrTcr
#print axioms Reduction.toClassicalWith_qrPre
#print axioms Reduction.toClassicalWith_qrUd
#print axioms Reduction.toClassicalWith_qToTcr
#print axioms Reduction.toClassicalWith_qToDspr
#print axioms Reduction.tendsto_betaEufFinal
#print axioms Reduction.slhdsa_euf_cma_final_quantum_machines_all
