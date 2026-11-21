import Reduction.TcrMemo

/-!
# The final theorems with class adversaries that do not recompute the key structure (package W5)

The four headline theorems of `Reduction/TightCapsHeadline.lean` (every SM game at its tight
target cap) restated with the four arity-class SM-TCR adversaries `bTcrArST n A` replaced by
`bTcrArM n A` (`Reduction/TcrMemo.lean`): same phase 1 (same targets, collection queries and
samples), phase 2 without the recomputation of the key structure — own hash evaluations after
the seed is revealed `≤ keygenHashes + qs·signHashes + 1 + 2·verifyHashes`
(`Resources2.memoForgeOpen_hashes`; `≤ 269824 + qs·2007385 + 7857` at SHA2-128s) instead of
`… + tcrTargets ≈ 2^79.81`.

The problem instances are those of the tight-cap theorems (`boundFinalTight`); the experiments
of `bTcrArM n A` and `bTcrArST n A` are equal (`bTcrArM_experiment_eq`), so the bound is *equal*
to the tight bound and to the split bound (`betaEufFinalMemo_eq`, `betaSufFinalMemo_eq`).

Main statements: `slhdsa_suf_cma_final_memo`, `slhdsa_euf_cma_final_memo`,
`slhdsa_pure_euf_cma_final_memo`, `slhdsa_pure_suf_cma_final_memo`; `∀`-forms (primed);
128s instances `slhdsa_sha2_128s_*_final_memo`; resources `final_memo_resources`,
`final_memo_resources_128s`.
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

-- as in `Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-- **The bound with the memoising class adversaries equals the tight bound** (any PRF
distinguishers `B₁`, `B₂`). -/
theorem boundFinalMemo_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) =
      boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArST 1 A) (bTcrArST 2 A) (bTcrArST vp.params.len A) (bTcrArST vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) := by
  unfold boundFinalTight
  rw [bTcrArM_advantage_eq hS 1 A, bTcrArM_advantage_eq hS 2 A,
    bTcrArM_advantage_eq hS vp.params.len A, bTcrArM_advantage_eq hS vp.params.k A]

/-- The final EUF-CMA bound (tight caps, class adversaries without structure recomputation)
as a function of the forger. -/
noncomputable def betaEufFinalMemo (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

/-- The final SUF-CMA bound (tight caps, class adversaries without structure recomputation)
as a function of the forger (the same program as the strong forger). -/
noncomputable def betaSufFinalMemo (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalTight pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

theorem betaEufFinalMemo_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    betaEufFinalMemo A = betaEufFinalTight A :=
  boundFinalMemo_eq hS A _ _

theorem betaSufFinalMemo_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    betaSufFinalMemo A = betaSufFinalTight A :=
  boundFinalMemo_eq hS A _ _

theorem betaEufFinalMemo_eq_split (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) : betaEufFinalMemo A = betaEufFinalSplit A :=
  (betaEufFinalMemo_eq hS A).trans (betaEufFinalTight_eq hS A)

theorem betaSufFinalMemo_eq_split (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) : betaSufFinalMemo A = betaSufFinalSplit A :=
  (betaSufFinalMemo_eq hS A).trans (betaSufFinalTight_eq hS A)

/-- **Standard-model SUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), every SM game at
its tight target cap, class adversaries without structure recomputation.**  For every strong forger `S`, with `A := S.toUnforgeableAdversary`:

`Adv^{SUF-CMA}(S) ≤ Adv^{PRF}_{PRF on SkAdrs}(bPrfWC sufCheck A)
   + Adv^{PRF}_{PRF_msg}(bPrfMsgWL sufCheck A) + Adv^{ITSR}_{H_msg}(bItsrL A)
   + Adv^{SM-DSPR}_{F}(toDspr (bOpenPreS A)) + 3·Adv^{SM-TCR}_{F}(toTcr (bOpenPreS A))
   + Adv^{SM-TCR}_{F}(bTcrArM 1 A) + Adv^{SM-TCR}_{H}(bTcrArM 2 A)
   + Adv^{SM-TCR}_{T_len}(bTcrArM len A) + Adv^{SM-TCR}_{T_k}(bTcrArM k A)
   + (w-2)·Adv^{SM-UD}_{F}(rUd (bWotsS A)) + Adv^{SM-PRE}_{F}(rPre (bWotsS A))
   + Adv^{SM-TCR}_{F}(rTcrT (bWotsS A))`,

where the class games accept at most `arityTargets vp n` targets and the chain game at most
`#inst · len · (w − 1)`. -/
theorem slhdsa_suf_cma_final_memo (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArM 1 S.toUnforgeableAdversary) (bTcrArM 2 S.toUnforgeableAdversary)
        (bTcrArM vp.params.len S.toUnforgeableAdversary)
        (bTcrArM vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) :=
  le_of_le_of_eq (slhdsa_suf_cma_final_tight hS S)
    (boundFinalMemo_eq hS S.toUnforgeableAdversary (bPrfWC sufCheck S.toUnforgeableAdversary)
      (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)).symm

/-- `slhdsa_suf_cma_final_memo` in the form `∀ S, Adv S ≤ β S`. -/
theorem slhdsa_suf_cma_final_memo' (hS : Structural vp prims) :
    ∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalMemo S.toUnforgeableAdversary :=
  fun S => slhdsa_suf_cma_final_memo hS S

/-- **Standard-model EUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), every SM game at
its tight target cap, class adversaries without structure recomputation.** -/
theorem slhdsa_euf_cma_final_memo (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) :=
  le_of_le_of_eq (slhdsa_euf_cma_final_tight hS A)
    (boundFinalMemo_eq hS A (bPrfC A) (Lazy.bPrfMsgL A)).symm

/-- `slhdsa_euf_cma_final_memo` in the form `∀ A, Adv A ≤ β A`. -/
theorem slhdsa_euf_cma_final_memo' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalMemo A :=
  fun A => slhdsa_euf_cma_final_memo hS A

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), tight caps, memoising class adversaries**: the tight
bound at the internal forger `toInternal A`. -/
theorem slhdsa_pure_euf_cma_final_memo (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC (toInternal A)) (Lazy.bPrfMsgL (toInternal A))
        (Lazy.bItsrL (toInternal A))
        (toDspr (Lazy.bOpenPreS (toInternal A))) (toTcr (Lazy.bOpenPreS (toInternal A)))
        (bTcrArM 1 (toInternal A)) (bTcrArM 2 (toInternal A))
        (bTcrArM vp.params.len (toInternal A)) (bTcrArM vp.params.k (toInternal A))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal A))) (rPre pkSeedDist (Lazy.bWotsS (toInternal A)))
        (rTcrT pkSeedDist (Lazy.bWotsS (toInternal A))) :=
  external_bound_of_internal_bound betaEufFinalMemo (slhdsa_euf_cma_final_memo' hS) A

/-- **SUF-CMA of the external pure interface, tight caps, memoising class adversaries**: the tight SUF bound at the internal
forger `toInternal S.toUnforgeableAdversary`. -/
theorem slhdsa_pure_suf_cma_final_memo (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bItsrL (toInternal S.toUnforgeableAdversary))
        (toDspr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (toTcr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (bTcrArM 1 (toInternal S.toUnforgeableAdversary))
        (bTcrArM 2 (toInternal S.toUnforgeableAdversary))
        (bTcrArM vp.params.len (toInternal S.toUnforgeableAdversary))
        (bTcrArM vp.params.k (toInternal S.toUnforgeableAdversary))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rPre pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rTcrT pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary))) :=
  le_of_le_of_eq (slhdsa_pure_suf_cma_final_tight hS S)
    (boundFinalMemo_eq hS (toInternal S.toUnforgeableAdversary)
      (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary))
      (Lazy.bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary))).symm

/-- `slhdsa_pure_euf_cma_final_memo` in the form `∀ A, Adv A ≤ β (toInternal A)`. -/
theorem slhdsa_pure_euf_cma_final_memo' (hS : Structural vp prims) :
    ∀ A : ExtForger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        betaEufFinalMemo (toInternal A) :=
  fun A => slhdsa_pure_euf_cma_final_memo hS A

/-- `slhdsa_pure_suf_cma_final_memo` in the form `∀ S, Adv S ≤ β (toInternal S.to…)`. -/
theorem slhdsa_pure_suf_cma_final_memo' (hS : Structural vp prims) :
    ∀ S : ExtStrongForger vp prims optRand pkSeedDist,
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  fun S => slhdsa_pure_suf_cma_final_memo hS S

/-- **Resources of the four class adversaries of the final bound.**  For every arity `n`:
phase 1 in the tight-cap class game registers exactly `arityTargets vp n` targets (the cap) and
makes `tcrTargets vp − arityTargets vp n` collection queries; phase 2, for every state
`(tbl, L)` and every game spec, is the interpretation of the open program `memoForgeOpen A L pk`
followed by the hash-free translation `classOut`; and that open program makes at most
`keygenHashes + qs·signHashes + (1 + 2·verifyHashes)` hash queries. -/
theorem final_memo_resources (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ n, Resources2.TcrPhase1Counts (bTcrArM n A) (arityTargets vp n) (tcrTargets vp)) ∧
    (∀ {ι : Type} (gspec : OracleSpec ι) (n : ℕ) (tbl : SecretTable vp prims)
        (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
      (liftM ((bTcrArM n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
        simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
          (Resources2.memoForgeOpen A L pk) >>= fun jm => pure (classOut prims n L jm)) ∧
    ∀ {ι : Type} (gspec : OracleSpec ι) (L : List (prims.AdrsKey × List prims.Y))
        (pk : prims.PkSeed),
      IsQueryBoundP (Resources2.memoForgeOpen (gspec := gspec) A L pk)
        (fun t => Lazy.kind t = .hash)
        (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)) :=
  ⟨fun n => bTcrArM_phase1 hS n A,
    fun _ n tbl L pk => Resources2.bTcrArM_forge_open n A tbl L pk,
    fun _ L pk => Resources2.memoForgeOpen_hashes A qs hA L pk⟩

end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction

open TweakableHash

/-- **SUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), final form.** -/
theorem slhdsa_sha2_128s_suf_cma_final_memo
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_memo structural_128s S

/-- **EUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), final form.** -/
theorem slhdsa_sha2_128s_euf_cma_final_memo
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalMemo A :=
  slhdsa_euf_cma_final_memo structural_128s A

/-- **EUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, final form.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final_memo
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : ExtForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal A) :=
  slhdsa_pure_euf_cma_final_memo structural_128s A

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, final form.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final_memo
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : ExtStrongForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final_memo structural_128s S

/-- **Resources of the class adversaries at SHA2-128s**: targets `533756792467910173399552`,
`528785142244921151848447`, `9241421688590303744`, `9223372036854775808` (`F`, `H`, `T_len`,
`T_k`; all structure calls `1062560399506556770327551`), and at most
`269824 + qs·2007385 + 7857` own hash evaluations after the seed is revealed. -/
theorem final_memo_resources_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    Resources2.TcrPhase1Counts (bTcrArM 1 A) 533756792467910173399552
        1062560399506556770327551 ∧
    Resources2.TcrPhase1Counts (bTcrArM 2 A) 528785142244921151848447
        1062560399506556770327551 ∧
    Resources2.TcrPhase1Counts (bTcrArM Link.vp.params.len A) 9241421688590303744
        1062560399506556770327551 ∧
    Resources2.TcrPhase1Counts (bTcrArM Link.vp.params.k A) 9223372036854775808
        1062560399506556770327551 ∧
    ∀ {ι : Type} (gspec : OracleSpec ι) (L : List (Link.prims.AdrsKey × List Link.prims.Y))
        (pk : Link.prims.PkSeed),
      IsQueryBoundP (Resources2.memoForgeOpen (gspec := gspec) A L pk)
        (fun t => Lazy.kind t = .hash) (269824 + qs * 2007385 + 7857) := by
  have h := fun n => bTcrArM_phase1 structural_128s n A
  have e := arityTargets_128s
  have t := Resources.tcrTargets_128s_val
  refine ⟨?_, ?_, ?_, ?_, fun gspec L pk =>
    Resources2.memoForgeOpen_hashes_128s optRand pkSeedDist A qs hA L pk⟩
  · have := h 1; rwa [e.1, t] at this
  · have := h 2; rwa [e.2.1, t] at this
  · have := h Link.vp.params.len; rwa [e.2.2.1, t] at this
  · have := h Link.vp.params.k; rwa [e.2.2.2.1, t] at this

#print axioms boundFinalMemo_eq
#print axioms slhdsa_suf_cma_final_memo
#print axioms slhdsa_euf_cma_final_memo
#print axioms slhdsa_pure_euf_cma_final_memo
#print axioms slhdsa_pure_suf_cma_final_memo
#print axioms slhdsa_suf_cma_final_memo'
#print axioms slhdsa_euf_cma_final_memo'
#print axioms slhdsa_pure_euf_cma_final_memo'
#print axioms slhdsa_pure_suf_cma_final_memo'
#print axioms final_memo_resources
#print axioms slhdsa_sha2_128s_suf_cma_final_memo
#print axioms slhdsa_sha2_128s_euf_cma_final_memo
#print axioms slhdsa_sha2_128s_pure_euf_cma_final_memo
#print axioms slhdsa_sha2_128s_pure_suf_cma_final_memo
#print axioms final_memo_resources_128s

end Reduction
