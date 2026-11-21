import Reduction.TightCaps

/-!
# The final theorems at tight target caps (package W2)

The four headline theorems of `Reduction/HeadlineSplit.lean` restated with every SM game at the
cap its adversary actually uses:

* the four arity-class SM-TCR games are `thashArityProblemT vp prims pkSeedDist n`
  (cap `arityTargets vp n`, attained exactly by `bTcrArST n A`: `bTcrArST_targets_eq_cap`)
  instead of `thashArityProblem … n` (cap `tcrTargets vp`);
* the chain SM-TCR(`F`) game is `wotsTcrProblemT vp prims pkSeedDist`
  (cap `#inst · len · (w − 1)`) instead of `wotsTcrProblem …` (cap `#inst · len · w`).

The adversaries `bTcrArST n A`, `rTcrT pkSeedDist W` are the old ones re-typed (same programs:
`bTcrArST_choose`, `bTcrArST_forge`, `rTcrT_choose`, `rTcrT_forge`), their experiments are equal
to the old ones (`bTcrArST_experiment_eq`, `rTcrT_experiment_eq`), so the tight bound *equals*
the split bound (`betaEufFinalTight_eq`, `betaSufFinalTight_eq`): nothing is lost, and the
assumptions are weaker (fewer admitted adversaries).

The other seven problem instances are unchanged: PRF games (`skPrfC`, `msgPrf`) and ITSR
(`itsrProblem`) have no cap; `forsDsprProblem`, `forsTcrProblem` have cap `2^h·k·2^a`, attained
(`Lazy.bOpenPreS_targets`); `wotsUdProblem`, `wotsPreProblem` have cap `#inst·len`, which is the
proved per-run bound (`Resources.rUd_challenges_le`, `rPre_challenges_le`).  See `status/W2.md`.

Main statements: `slhdsa_suf_cma_final_tight`, `slhdsa_euf_cma_final_tight`,
`slhdsa_pure_euf_cma_final_tight`, `slhdsa_pure_suf_cma_final_tight`; `∀`-forms
`slhdsa_{suf,euf}_cma_final_tight'`; 128s instances `slhdsa_sha2_128s_*_final_tight`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable [Fintype prims.Y]

/-- The right-hand side of the tight-cap final theorems: `boundFinalSplit` with the four class
games and the chain SM-TCR game at their tight caps (twelve advantages). -/
noncomputable def boundFinalTight (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (T : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist)) : ℝ≥0∞ :=
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.advantage D +
      3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    (SM_DT_TCR_Advantage C₁ + SM_DT_TCR_Advantage C₂ + SM_DT_TCR_Advantage C₃ +
      SM_DT_TCR_Advantage C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ +
    SM_DT_PRE_Advantage B₇ +
    SM_DT_TCR_Advantage B₈

/-- **The tight bound equals the split bound** at the reduction's adversaries (any PRF
distinguishers `B₁`, `B₂`). -/
theorem boundFinalTight_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArST 1 A) (bTcrArST 2 A) (bTcrArST vp.params.len A) (bTcrArST vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) =
      boundFinalSplit pkSeedDist B₁ B₂ (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArS 1 A) (bTcrArS 2 A) (bTcrArS vp.params.len A) (bTcrArS vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A)) := by
  unfold boundFinalTight boundFinalSplit
  rw [bTcrArST_advantage_eq hS 1 A, bTcrArST_advantage_eq hS 2 A,
    bTcrArST_advantage_eq hS vp.params.len A, bTcrArST_advantage_eq hS vp.params.k A,
    rTcrT_advantage_eq hS (Lazy.bWotsS A)]

/-- The tight EUF-CMA bound as a function of the forger. -/
noncomputable def betaEufFinalTight (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArST 1 A) (bTcrArST 2 A) (bTcrArST vp.params.len A) (bTcrArST vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

/-- The tight SUF-CMA bound as a function of the forger (the same program as the strong
forger). -/
noncomputable def betaSufFinalTight (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalTight pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArST 1 A) (bTcrArST 2 A) (bTcrArST vp.params.len A) (bTcrArST vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

theorem betaEufFinalTight_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    betaEufFinalTight A = betaEufFinalSplit A :=
  boundFinalTight_eq hS A _ _

theorem betaSufFinalTight_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    betaSufFinalTight A = betaSufFinalSplit A :=
  boundFinalTight_eq hS A _ _

/-- **Standard-model SUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), every SM game at
its tight target cap.**  For every strong forger `S`, with `A := S.toUnforgeableAdversary`:

`Adv^{SUF-CMA}(S) ≤ Adv^{PRF}_{PRF on SkAdrs}(bPrfWC sufCheck A)
   + Adv^{PRF}_{PRF_msg}(bPrfMsgWL sufCheck A) + Adv^{ITSR}_{H_msg}(bItsrL A)
   + Adv^{SM-DSPR}_{F}(toDspr (bOpenPreS A)) + 3·Adv^{SM-TCR}_{F}(toTcr (bOpenPreS A))
   + Adv^{SM-TCR}_{F}(bTcrArST 1 A) + Adv^{SM-TCR}_{H}(bTcrArST 2 A)
   + Adv^{SM-TCR}_{T_len}(bTcrArST len A) + Adv^{SM-TCR}_{T_k}(bTcrArST k A)
   + (w-2)·Adv^{SM-UD}_{F}(rUd (bWotsS A)) + Adv^{SM-PRE}_{F}(rPre (bWotsS A))
   + Adv^{SM-TCR}_{F}(rTcrT (bWotsS A))`,

where the class games accept at most `arityTargets vp n` targets and the chain game at most
`#inst · len · (w − 1)`. -/
theorem slhdsa_suf_cma_final_tight (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArST 1 S.toUnforgeableAdversary) (bTcrArST 2 S.toUnforgeableAdversary)
        (bTcrArST vp.params.len S.toUnforgeableAdversary)
        (bTcrArST vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) :=
  (slhdsa_suf_cma_final_split hS S).trans
    (boundFinalTight_eq hS S.toUnforgeableAdversary _ _).ge

/-- `slhdsa_suf_cma_final_tight` in the form `∀ S, Adv S ≤ β S`. -/
theorem slhdsa_suf_cma_final_tight' (hS : Structural vp prims) :
    ∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalTight S.toUnforgeableAdversary :=
  fun S => slhdsa_suf_cma_final_tight hS S

/-- **Standard-model EUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), every SM game at
its tight target cap.** -/
theorem slhdsa_euf_cma_final_tight (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArST 1 A) (bTcrArST 2 A) (bTcrArST vp.params.len A) (bTcrArST vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) :=
  (slhdsa_euf_cma_final_split hS A).trans (boundFinalTight_eq hS A _ _).ge

/-- `slhdsa_euf_cma_final_tight` in the form `∀ A, Adv A ≤ β A`. -/
theorem slhdsa_euf_cma_final_tight' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalTight A :=
  fun A => slhdsa_euf_cma_final_tight hS A

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), tight caps**: the tight
bound at the internal forger `toInternal A`. -/
theorem slhdsa_pure_euf_cma_final_tight (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC (toInternal A)) (Lazy.bPrfMsgL (toInternal A))
        (Lazy.bItsrL (toInternal A))
        (toDspr (Lazy.bOpenPreS (toInternal A))) (toTcr (Lazy.bOpenPreS (toInternal A)))
        (bTcrArST 1 (toInternal A)) (bTcrArST 2 (toInternal A))
        (bTcrArST vp.params.len (toInternal A)) (bTcrArST vp.params.k (toInternal A))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal A))) (rPre pkSeedDist (Lazy.bWotsS (toInternal A)))
        (rTcrT pkSeedDist (Lazy.bWotsS (toInternal A))) :=
  external_bound_of_internal_bound betaEufFinalTight (slhdsa_euf_cma_final_tight' hS) A

/-- **SUF-CMA of the external pure interface, tight caps**: the tight SUF bound at the internal
forger `toInternal S.toUnforgeableAdversary`. -/
theorem slhdsa_pure_suf_cma_final_tight (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bItsrL (toInternal S.toUnforgeableAdversary))
        (toDspr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (toTcr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (bTcrArST 1 (toInternal S.toUnforgeableAdversary))
        (bTcrArST 2 (toInternal S.toUnforgeableAdversary))
        (bTcrArST vp.params.len (toInternal S.toUnforgeableAdversary))
        (bTcrArST vp.params.k (toInternal S.toUnforgeableAdversary))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rPre pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rTcrT pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary))) :=
  (slhdsa_pure_suf_cma_final_split hS S).trans
    (boundFinalTight_eq hS (toInternal S.toUnforgeableAdversary) _ _).ge

/-- `slhdsa_pure_euf_cma_final_tight` in the form `∀ A, Adv A ≤ β (toInternal A)`. -/
theorem slhdsa_pure_euf_cma_final_tight' (hS : Structural vp prims) :
    ∀ A : ExtForger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        betaEufFinalTight (toInternal A) :=
  fun A => slhdsa_pure_euf_cma_final_tight hS A

/-- `slhdsa_pure_suf_cma_final_tight` in the form `∀ S, Adv S ≤ β (toInternal S.to…)`. -/
theorem slhdsa_pure_suf_cma_final_tight' (hS : Structural vp prims) :
    ∀ S : ExtStrongForger vp prims optRand pkSeedDist,
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalTight (toInternal S.toUnforgeableAdversary) :=
  fun S => slhdsa_pure_suf_cma_final_tight hS S

/-- **Target usage of the five re-capped adversaries in their tight games**: each class
adversary accepts exactly its cap in every run; the chain adversary at most its cap. -/
theorem final_tight_resources (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    (∀ n pk, ∀ z ∈ support ((simulateQ
        (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArST n A).choose).run ([], [])),
      z.2.1.length = (thashArityProblemT vp prims pkSeedDist n).numTargets) ∧
    ∀ pk, ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
        (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose).run ([], [])),
      z.2.1.length ≤ (wotsTcrProblemT vp prims pkSeedDist).numTargets :=
  ⟨fun n pk => bTcrArST_targets_eq_cap hS n A pk,
    fun pk => rTcrT_targets_le hS (Lazy.bWotsS A) pk⟩

end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction

open TweakableHash

/-- **SUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), tight caps.** -/
theorem slhdsa_sha2_128s_suf_cma_final_tight
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalTight S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_tight structural_128s S

/-- **EUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), tight caps.** -/
theorem slhdsa_sha2_128s_euf_cma_final_tight
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalTight A :=
  slhdsa_euf_cma_final_tight structural_128s A

/-- **EUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, tight caps.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final_tight
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : ExtForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalTight (toInternal A) :=
  slhdsa_pure_euf_cma_final_tight structural_128s A

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, tight caps.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final_tight
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : ExtStrongForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalTight (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final_tight structural_128s S

#print axioms boundFinalTight_eq
#print axioms slhdsa_suf_cma_final_tight
#print axioms slhdsa_euf_cma_final_tight
#print axioms slhdsa_pure_euf_cma_final_tight
#print axioms slhdsa_pure_suf_cma_final_tight
#print axioms slhdsa_suf_cma_final_tight'
#print axioms slhdsa_euf_cma_final_tight'
#print axioms slhdsa_pure_euf_cma_final_tight'
#print axioms slhdsa_pure_suf_cma_final_tight'
#print axioms final_tight_resources
#print axioms slhdsa_sha2_128s_suf_cma_final_tight
#print axioms slhdsa_sha2_128s_euf_cma_final_tight
#print axioms slhdsa_sha2_128s_pure_euf_cma_final_tight
#print axioms slhdsa_sha2_128s_pure_suf_cma_final_tight

end Reduction
