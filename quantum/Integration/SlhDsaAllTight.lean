import Integration.SlhDsaAll

/-!
# SLH-DSA against ALL quantum forgers: the tight-cap headlines, unconditionally (integration)

NOT part of the default target; checked by `scripts/check-integration.sh`.

Quantum versions WITHOUT the hypothesis `RationalBorn` of the four tight-cap headlines of
`security/Reduction/TightCapsHeadline.lean` (class adversaries `bTcrArST n`, which recompute the
key structure in phase 2; the memoising variants `bTcrArM n` are in `Integration/SlhDsaAll.lean`):

* `slhdsa_euf_cma_final_tight_quantum_all`, `slhdsa_suf_cma_final_tight_quantum_all`
  (internal scheme),
* `slhdsa_pure_euf_cma_final_tight_quantum_all`, `slhdsa_pure_suf_cma_final_tight_quantum_all`
  (external pure interface).

They supersede the `RationalBorn` versions `slhdsa_*_final_tight_quantum` of
`Integration/SlhDsaQuantumTight.lean`: same right-hand sides `qBetaEufTight` / `qBetaSufTight`
(twelve quantum advantages of explicit machines running the forger once), every quantum forger.

Proof pattern as in `Integration/SlhDsaAll.lean`; the only new program equality is
`toClassicalWith_qbTcrArST` (for every sampler, the classical approximant of `qbTcrArST n Q` is
`bTcrArST n` at the approximant of `Q`), obtained through the abstract lemma
`toClassicalWith_qTcrOfClassical` so that no unification problem unfolds the concrete adversaries.
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
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

-- as in `security/Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-! ## The program equality for an arbitrary sampler -/

section programs

variable (s : Sampler W)

theorem toProbCompCWith_qbTcrS_forge (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    toProbCompCWith s ((qbTcrS Q).forge tbl pkSeed) Q.ρ₀ =
      (Lazy.bTcrS (Q.toClassicalWith s)).forge tbl pkSeed := by
  change toProbCompCWith s (_ >>= fun r => liftU _) Q.ρ₀ = _
  rw [toProbCompCWith_bind_liftU, toProbCompCWith_close _ _ (forwardsUnif_ofLift_add _)]
  rfl

theorem toProbCompCWith_qTcrArForge (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    toProbCompCWith s (qTcrArForge n Q st pk) Q.ρ₀ =
      (bTcrArST n (Q.toClassicalWith s)).forge st pk := by
  rw [qTcrArForge, toProbCompCWith_bind_liftU, toProbCompCWith_qbTcrS_forge, bTcrArST_forge]
  exact (restrict_forge (fun xs : List prims.Y => xs.length = n) (arityDefault prims n)
    (Lazy.bTcrS (Q.toClassicalWith s)) st pk).symm

theorem bTcrArST_State_eq (n : ℕ) (A₁ A₂ : Forger vp prims optRand pkSeedDist) :
    (bTcrArST n A₁).State = (bTcrArST n A₂).State := rfl

/-- The `choose` phase of `bTcrArST n A` does not depend on the forger `A`. -/
theorem bTcrArST_choose_eq (n : ℕ) (A₁ A₂ : Forger vp prims optRand pkSeedDist) :
    (bTcrArST n A₁).choose = (bTcrArST n A₂).choose := rfl

/-- Generic in the two forgers (no unification problem compares two concrete forgers). -/
theorem toClassicalWith_qTcrOfClassical_bTcrArST (n : ℕ)
    (A₁ A₂ : Forger vp prims optRand pkSeedDist)
    (qf : SecretTable vp prims × List (prims.AdrsKey × List prims.Y) → prims.PkSeed →
      Closed W (ℕ × {xs : List prims.Y // xs.length = n}))
    (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1)
    (h : ∀ st pk, toProbCompCWith s (qf st pk) ρ₀ = (bTcrArST n A₂).forge st pk) :
    (qTcrOfClassical (bTcrArST n A₁) qf ρ₀ h₁ h₂).toClassicalWith s = bTcrArST n A₂ :=
  toClassicalWith_qTcrOfClassical s (bTcrArST n A₁) (bTcrArST n A₂) qf ρ₀ h₁ h₂
    (bTcrArST_State_eq n A₁ A₂) (heq_of_eq (bTcrArST_choose_eq n A₁ A₂))
    (heq_of_eq (funext fun st => funext fun pk => h st pk))

/-- For every sampler, the classical approximant of the quantum tight-cap class adversary is the
classical tight-cap class adversary at the approximant of the forger. -/
theorem toClassicalWith_qbTcrArST (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    (qbTcrArST n Q).toClassicalWith s = bTcrArST n (Q.toClassicalWith s) :=
  toClassicalWith_qTcrOfClassical_bTcrArST s n _ _ _ _ _ _
    fun st pk => toProbCompCWith_qTcrArForge s n Q st pk

end programs

/-! ## Limits -/

section limits

variable {samp : ℕ → Sampler W} (hs : BornApprox samp)
  (Q : QForger W (internalAlg vp prims optRand pkSeedDist))

include hs

theorem tendsto_tcr_bTcrArST (k : ℕ) :
    Tendsto (fun n ↦ SM_DT_TCR_Advantage (bTcrArST k (Q.toClassicalWith (samp n)))) atTop
      (𝓝 (qSM_DT_TCR_Advantage (qbTcrArST k Q))) := by
  simp only [← toClassicalWith_qbTcrArST]
  exact tendsto_SM_DT_TCR_Advantage hs _

/-- The tight bound at the approximants converges to the quantum tight bound (any PRF
distinguisher sequences whose advantages converge). -/
theorem tendsto_boundFinalTight
    (B₁ : ℕ → PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : ℕ → MsgPrfAdv prims) {P₁ P₂ : ℝ≥0∞}
    (h₁ : Tendsto (fun n ↦ (skPrfC vp prims).prfAdvantage (B₁ n)) atTop (𝓝 P₁))
    (h₂ : Tendsto (fun n ↦ (msgPrf vp prims).prfAdvantage (B₂ n)) atTop (𝓝 P₂)) :
    Tendsto (fun n ↦ boundFinalTight pkSeedDist (B₁ n) (B₂ n)
        (Lazy.bItsrL (Q.toClassicalWith (samp n)))
        (toDspr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (toTcr (Lazy.bOpenPreS (Q.toClassicalWith (samp n))))
        (bTcrArST 1 (Q.toClassicalWith (samp n))) (bTcrArST 2 (Q.toClassicalWith (samp n)))
        (bTcrArST vp.params.len (Q.toClassicalWith (samp n)))
        (bTcrArST vp.params.k (Q.toClassicalWith (samp n)))
        (rUd pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))
        (rPre pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))
        (rTcrT pkSeedDist (Lazy.bWotsS (Q.toClassicalWith (samp n))))) atTop
      (𝓝 (qBoundTight Q P₁ P₂)) := by
  unfold boundFinalTight qBoundTight
  have hC := (((tendsto_tcr_bTcrArST hs Q 1).add (tendsto_tcr_bTcrArST hs Q 2)).add
    (tendsto_tcr_bTcrArST hs Q vp.params.len)).add (tendsto_tcr_bTcrArST hs Q vp.params.k)
  have hF := (tendsto_dspr_toDspr hs Q).add
    (ENNReal.Tendsto.const_mul (a := (3 : ℝ≥0∞)) (tendsto_tcr_toTcr hs Q) (Or.inr (by simp)))
  have hU := ENNReal.Tendsto.const_mul (a := ((vp.params.w - 2 : ℕ) : ℝ≥0∞))
    (tendsto_ud_rUd hs Q) (Or.inr (ENNReal.natCast_ne_top _))
  exact ((((((h₁.add h₂).add (tendsto_itsrAdvantage_bItsrL hs Q)).add hF).add hC).add hU).add
    (tendsto_pre_rPre hs Q)).add (tendsto_tcr_rTcrT hs Q)

theorem tendsto_betaEufFinalTight :
    Tendsto (fun n ↦ betaEufFinalTight (Q.toClassicalWith (samp n))) atTop
      (𝓝 (qBetaEufTight Q)) :=
  tendsto_boundFinalTight hs Q _ _ (tendsto_prfAdvantage_bPrfC hs Q)
    (tendsto_prfAdvantage_bPrfMsgL hs Q)

theorem tendsto_betaSufFinalTight :
    Tendsto (fun n ↦ betaSufFinalTight (Q.toClassicalWith (samp n))) atTop
      (𝓝 (qBetaSufTight Q)) :=
  tendsto_boundFinalTight hs Q _ _ (tendsto_prfAdvantage_bPrfWC hs Q sufCheck)
    (tendsto_prfAdvantage_bPrfMsgWL hs Q sufCheck)

end limits

/-! ## Lifting lemmas -/

section lifting

variable {Mb PKb SKb Sb : Type} {balg : SignatureAlg ProbComp Mb PKb SKb Sb}

theorem euf_tight_all (Q : QForger W balg)
    (T : SignatureAlg.UnforgeableAdversary balg → Forger vp prims optRand pkSeedDist)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hT : ∀ s, qT.toClassicalWith s = T (Q.toClassicalWith s))
    (h : ∀ A, SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalTight (T A)) :
    qUnforgeableAdvantage Q ≤ qBetaEufTight qT := by
  refine le_of_forall_classical_of_tendsto
    (f := fun A ↦ SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A)
    (g := fun A ↦ betaEufFinalTight (T A)) h (fun n ↦ Q.toClassicalWith (sampN n))
    (tendsto_unforgeableAdvantage bornApprox_sampN Q) ?_
  simp only [← hT]
  exact tendsto_betaEufFinalTight bornApprox_sampN qT

theorem suf_tight_all (Q : QForger W balg)
    (T : SignatureAlg.UnforgeableAdversary balg → Forger vp prims optRand pkSeedDist)
    (qT : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hT : ∀ s, qT.toClassicalWith s = T (Q.toClassicalWith s))
    (h : ∀ S : SignatureAlg.StrongUnforgeableAdversary balg,
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalTight (T S.toUnforgeableAdversary)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufTight qT := by
  refine le_of_forall_classical_of_tendsto
    (f := fun S ↦ SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S)
    (g := fun S ↦ betaSufFinalTight (T S.toUnforgeableAdversary)) h
    (fun n ↦ Q.toClassicalStrongWith (sampN n))
    (tendsto_strongUnforgeableAdvantage bornApprox_sampN Q) ?_
  have e : ∀ n, (Q.toClassicalStrongWith (sampN n)).toUnforgeableAdversary =
      Q.toClassicalWith (sampN n) := fun _ ↦ rfl
  simp only [e, ← hT]
  exact tendsto_betaSufFinalTight bornApprox_sampN qT

end lifting

/-! ## Headlines -/

/-- **EUF-CMA of SLH-DSA (internal algorithms) against every quantum forger, tight caps.**
Supersedes `slhdsa_euf_cma_final_tight_quantum` (no `RationalBorn`). -/
theorem slhdsa_euf_cma_final_tight_quantum_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufTight Q :=
  euf_tight_all Q id Q (fun _ ↦ rfl) (slhdsa_euf_cma_final_tight' hS)

/-- **SUF-CMA of SLH-DSA (internal algorithms) against every quantum forger, tight caps.** -/
theorem slhdsa_suf_cma_final_tight_quantum_all (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufTight Q :=
  suf_tight_all Q id Q (fun _ ↦ rfl) (slhdsa_suf_cma_final_tight' hS)

/-- **EUF-CMA of the external pure interface against every quantum forger, tight caps.** -/
theorem slhdsa_pure_euf_cma_final_tight_quantum_all (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufTight (qToInternal Q) :=
  euf_tight_all Q toInternal (qToInternal Q) (fun s ↦ toClassicalWith_qToInternal s Q)
    (slhdsa_pure_euf_cma_final_tight' hS)

/-- **SUF-CMA of the external pure interface against every quantum forger, tight caps.** -/
theorem slhdsa_pure_suf_cma_final_tight_quantum_all (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufTight (qToInternal Q) :=
  suf_tight_all Q toInternal (qToInternal Q) (fun s ↦ toClassicalWith_qToInternal s Q)
    (slhdsa_pure_suf_cma_final_tight' hS)

end Reduction

#print axioms Reduction.toClassicalWith_qbTcrArST
#print axioms Reduction.slhdsa_euf_cma_final_tight_quantum_all
#print axioms Reduction.slhdsa_suf_cma_final_tight_quantum_all
#print axioms Reduction.slhdsa_pure_euf_cma_final_tight_quantum_all
#print axioms Reduction.slhdsa_pure_suf_cma_final_tight_quantum_all
