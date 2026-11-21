import Reduction.Final
import Reduction.PrfDomain
import Reduction.Lazy.MsgLazy
import Reduction.Lazy.ItsrLazy
import Reduction.Lazy.OpenPreSparse
import Reduction.Lazy.TcrSparse
import Reduction.Lazy.WotsSparse

/-!
# The final theorem, version 2: canonical-domain PRF game, no eager table

`slhdsa_euf_cma_v2` is `slhdsa_euf_cma` with

* the PRF term taken in the game `skPrfC` whose oracle domain is the secret-key address subtype
  `SkAdrs vp` (`Reduction.PrfDomain`); the old game `skPrf` is trivially winnable at SHA2-128s
  (`skPrf_broken_128s`, `Reduction.PrfDomainNonVacuity`), the new one is not attackable by that
  distinguisher (`not_skDom_256`, `sha2PRFChecked_ok_128s`);
* every reduction adversary free of the eager `2 ^ 256`-cell table `sampleTable`:
  `bPrfC` (never had a table), `Lazy.bPrfMsgL`, `Lazy.bItsrL` (lazy association-list cache, work
  polynomial in the number of signing queries), `Lazy.bOpenPreS`, `Lazy.bTcrS`, `Lazy.bWotsS`
  (sparse tables: one uniform value per secret cell of the key structure that the adversary can
  read, `default` elsewhere).

What is and is not efficient (see `status/A.md` for the resource table):

* `bPrfC`, `bPrfMsgL`, `bItsrL`: game queries, fresh samples and hash evaluations of key
  generation and signing are bounded by explicit polynomials in `qs` (`slhdsa_euf_cma_v2_resources`,
  `Lazy.bPrfMsgL_draws`, `Lazy.bPrfMsgL_hashes`, `Lazy.bItsrL_draws`, `Lazy.bItsrL_hashes`).
* `bOpenPreS`, `bTcrS`, `bWotsS` (hence `rUd`, `rPre`, `rTcr`) still walk the whole key structure
  (`2^h` FORS instances, all XMSS trees): in every SM game of the bound the targets/commitments
  are fixed in a phase that does not know `PK.seed`, while the forger needs `PK.seed` before its
  first query, so all targets must be fixed before the forger runs.  This is the paper's
  reduction; it is not polynomial in `qs`.  The sparse tables are functions defined by a list
  lookup (`Tables.updateList`); the cost of local computation of these three adversaries is not
  formalised here.  (Later: `Reduction/Resources2*.lean` count their own hash evaluations after
  the seed is revealed; in particular `bTcrS A` recomputes the whole key structure there,
  `tcrTargets vp ≈ 2^79.81` evaluations at 128s, `Resources2.tcr_structure_exact`.)
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The right-hand side of the version-2 theorem: `bound` with the PRF advantage taken in the
canonical-domain game `skPrfC`. -/
noncomputable def boundV2 (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (B₄ : TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist))
    (B₅ : TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (B₆ : TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage B₄ +
    TweakableHash.SM_DT_TCR_Advantage B₅ +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * TweakableHash.SM_DT_UD_Advantage B₆ +
    TweakableHash.SM_DT_PRE_Advantage B₇ +
    TweakableHash.SM_DT_TCR_Advantage B₈

/-- The version-2 bound as a function of the forger. -/
noncomputable def betaV2 (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundV2 pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A) (Lazy.bOpenPreS A)
    (Lazy.bTcrS A) (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A))

/-- **Standard-model EUF-CMA security of SLH-DSA, version 2.**  (Intermediate; the final form
with the FORS term `SM-DSPR + 3·SM-TCR` and per-function SM-TCR terms is
`Reduction.slhdsa_euf_cma_final_split`.)  As `slhdsa_euf_cma`, with the PRF
game on the secret-key address domain and reduction adversaries that sample no eager table. -/
theorem slhdsa_euf_cma_v2 (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundV2 pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A) (Lazy.bOpenPreS A)
        (Lazy.bTcrS A) (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A)) := by
  have h := final_of_steps A (bPrf A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A) (Lazy.bOpenPreS A)
    (Lazy.bTcrS A) (Lazy.bWotsS A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A))
    (stepPRF hS A) (Lazy.stepPRFmsg_lazy A) (stepSplit A) (Lazy.stepITSR_lazy A)
    (Lazy.stepOpenPRE_sparse hS A) (Lazy.stepTCR_sparse hS A)
    (Lazy.stepWotsEmbed_sparse hS A) (stepWotsUD hS pkSeedDist (Lazy.bWotsS A))
    (stepWotsFinal hS pkSeedDist (Lazy.bWotsS A))
  unfold bound at h
  unfold boundV2
  rw [prfAdvantageC_eq hS.bounds]
  exact h

/-- The same statement in the form `∀ A, Adv A ≤ β A` (for
`Reduction.external_bound_of_internal_bound`). -/
theorem slhdsa_euf_cma_v2' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaV2 A :=
  fun A => slhdsa_euf_cma_v2 hS A

/-- **Version 2 with the `qs`-dependent resources.**  For a forger making at most `qs` signing
queries: the bound, and the game-query counts of the three `qs`-polynomial adversaries and the
opening count of `bOpenPreS`. -/
theorem slhdsa_euf_cma_v2_resources (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaV2 A ∧
      IsQueryBoundP (bPrfC A) (fun i => i.isRight = true)
        (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) ∧
      IsQueryBoundP (Lazy.bPrfMsgL A) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (Lazy.bItsrL A).main (fun i => i.isRight = true) qs ∧
      ∀ st pkSeed ys, IsQueryBoundP ((Lazy.bOpenPreS A).find st pkSeed ys)
        (fun i => i.isRight = true) (qs * vp.params.k) :=
  ⟨slhdsa_euf_cma_v2 hS A, bPrfC_queryBound_exact A qs hA, Lazy.bPrfMsgL_queryBound A qs hA,
    Lazy.bItsrL_queryBound A qs hA, fun st pkSeed ys =>
      Lazy.bOpenPreS_find_queryBound A qs hA st pkSeed ys⟩

#print axioms slhdsa_euf_cma_v2
#print axioms slhdsa_euf_cma_v2_resources

end Reduction
