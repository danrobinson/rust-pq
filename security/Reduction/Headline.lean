import Reduction.FinalV2
import Reduction.Instance128sV2
import Reduction.ForsTightFinal
import Reduction.SufPrfV2
import Reduction.Lazy.SufMsgLazy
import Reduction.SufSparse
import Reduction.ExternalSuf

/-!
# The final theorems (phase 2)

(The documented headline is `Reduction/HeadlineSplit.lean`: the same four theorems with the
cross-arity SM-TCR(`Thash`) term `B₅` below replaced by four per-function SM-TCR terms.  The
theorems of this file are unchanged and still proved.)

Everything here is a composition of the phase-2 packages; no new game and no new reduction idea.

**Bound.**  `boundFinal` is the right-hand side of every theorem of this file:

`Adv^{PRF}_{PRF on SkAdrs}(B₁) + Adv^{PRF}_{PRF_msg}(B₂) + Adv^{ITSR}_{H_msg}(B₃)
   + (Adv^{SM-DSPR}_{F}(D) + 3·Adv^{SM-TCR}_{F}(T)) + Adv^{SM-TCR}_{Thash}(B₅)
   + (w-2)·Adv^{SM-UD}_{F}(B₆) + Adv^{SM-PRE}_{F}(B₇) + Adv^{SM-TCR}_{F}(B₈)`

i.e. `Reduction.bound` (phase 1) with (i) the PRF game on the secret-key address domain `SkAdrs vp`
(`skPrfC`; the phase-1 game `skPrf` on all of `Adrs` is false at SHA2-128s,
`skPrf_broken_128s`), and (ii) the FORS-leaf term `SM-DT-OpenPRE(F)` replaced by
`SM-DSPR(F) + 3·SM-TCR(F)` (`forsOpenPre_le`).

**Theorems** (generic in `vp`, `prims`; hypothesis `Structural vp prims`, proved at SHA2-128s).

* `slhdsa_suf_cma_final` — strong unforgeability of the internal scheme
  `internalAlg vp prims optRand pkSeedDist` (`realAlg` is an abbreviation of the same term).
* `slhdsa_euf_cma_final` — EUF-CMA of the internal scheme (directly from `slhdsa_euf_cma_v2`;
  `slhdsa_euf_cma_final_of_suf` is the form that follows from SUF-CMA ≥ EUF-CMA).
* `slhdsa_pure_euf_cma_final`, `slhdsa_pure_suf_cma_final` — the external pure interface
  `externalAlg` (FIPS 205 Alg. 22/24, context strings), EUF-CMA and SUF-CMA.
* `final_resources` — proved query/target/commitment/opening/sample counts of every adversary
  occurring in these bounds, in closed form; `final_resources_128s` with numerals.
* `slhdsa_sha2_128s_*_final` — the instances at SLH-DSA-SHA2-128s, without hypothesis.

**Adversaries.**  No adversary of the final bounds reaches the eager table `sampleTable` or a
choice principle (`scratch/Final/FinalCheck.lean`).  The two PRF distinguishers differ between
the EUF-CMA and the SUF-CMA theorem only in harness and output bit (`bPrfC`/`bPrfMsgL` versus
`bPrfWC sufCheck`/`bPrfMsgWL sufCheck`); the other seven adversaries are the same.

**What is efficient and what is not.**  With `qs` the number of signing queries of the forger:

* polynomial in `qs` (proved counts of game queries, fresh samples and hash evaluations of key
  generation and signing): the PRF, PRF_msg and ITSR adversaries;
* NOT polynomial in `qs`: the six adversaries of the SM games (`toDspr`/`toTcr` of `bOpenPreS`,
  `bTcrS`, `rUd`/`rPre`/`rTcr` of `bWotsS`).  They walk the whole key structure and register
  between `≈ 2^68` and `≈ 2^80` targets at SHA2-128s, independently of `qs`.  This is inherent in
  the SM games, in which all targets are registered before `PK.seed` is revealed, while the
  forger needs `PK.seed` before its first query; it is the reduction of Hülsing–Kudinov and of
  the EasyCrypt proof.
* VCVio has no cost model for local computation: the counts are of oracle queries, of uniform
  samples, and (for the three lazy adversaries, where hashing is modelled as queries) of hash
  evaluations.  No running-time statement is made.
* The SM adversaries' own hashing is not small either.  `Reduction/Resources2*.lean` (later)
  count their hash evaluations after the seed is revealed: `bTcrS A` (and each `bTcrArS n A` of
  `Reduction/HeadlineSplit.lean`) recomputes the whole key structure, exactly `tcrTargets vp`
  (`≈ 2^79.81` at SHA2-128s) evaluations (`Resources2.tcr_structure_exact`); the FORS-leaf and
  chain adversaries hash `poly(qs)` in that phase but carry structure-size state and list work.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The bound -/

/-- The right-hand side of the final theorems: nine advantages in eight games.
`[Fintype prims.Y]` is needed only to state the SM-DSPR game (its winning condition quantifies
over second preimages). -/
noncomputable def boundFinal (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (T : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))
    (B₅ : SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.advantage D +
      3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    SM_DT_TCR_Advantage B₅ +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ +
    SM_DT_PRE_Advantage B₇ +
    SM_DT_TCR_Advantage B₈

/-- The final EUF-CMA bound as a function of the forger. -/
noncomputable def betaEufFinal (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinal pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A)) (Lazy.bTcrS A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A))

/-- The final SUF-CMA bound as a function of the forger (regarded as an EUF-CMA forger, i.e. the
same program): as `betaEufFinal`, with the PRF distinguishers of the strong-forgery check. -/
noncomputable def betaSufFinal (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinal pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A)) (Lazy.bTcrS A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcr pkSeedDist (Lazy.bWotsS A))

/-- Arithmetic of the composition: the two PRF terms, plus six terms with the OpenPRE summand
bounded by `d + 3·t`. -/
private theorem compose_le {a b c o d t e u f g : ℝ≥0∞} (ho : o ≤ d + 3 * t) :
    a + b + (c + o + e + u + f + g) ≤ a + b + c + (d + 3 * t) + e + u + f + g := by
  calc a + b + (c + o + e + u + f + g) = a + b + c + o + e + u + f + g := by ring
    _ ≤ a + b + c + (d + 3 * t) + e + u + f + g := by gcongr

/-! ## Internal scheme -/

/-- **Standard-model SUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), final form.**

For every strong forger `S` against `internalAlg vp prims optRand pkSeedDist` (it wins with a
valid `(message, signature)` pair that the signing oracle never returned; a new signature on a
signed message counts), with `A := S.toUnforgeableAdversary` (the same program):

`Adv^{SUF-CMA}(S) ≤ Adv^{PRF}_{PRF on SkAdrs}(bPrfWC sufCheck A)
   + Adv^{PRF}_{PRF_msg}(bPrfMsgWL sufCheck A) + Adv^{ITSR}_{H_msg}(bItsrL A)
   + Adv^{SM-DSPR}_{F}(toDspr (bOpenPreS A)) + 3·Adv^{SM-TCR}_{F}(toTcr (bOpenPreS A))
   + Adv^{SM-TCR}_{Thash}(bTcrS A) + (w-2)·Adv^{SM-UD}_{F}(rUd (bWotsS A))
   + Adv^{SM-PRE}_{F}(rPre (bWotsS A)) + Adv^{SM-TCR}_{F}(rTcr (bWotsS A))`.

No cryptographic hypothesis; `Structural` is the non-cryptographic encoding hypothesis proved at
SHA2-128s.  The right-hand advantages are not bounded here.  Holds for every `optRand`
(deterministic and hedged signing) and every `pkSeedDist`.  Resources: `final_resources`. -/
theorem slhdsa_suf_cma_final (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinal pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (Lazy.bTcrS S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcr pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) := by
  have h1 := suf_le_prf_add_g2 hS S
  have h2 := g2W_le_g2BoundS hS sufCheck (fun _ _ _ h => h) S.toUnforgeableAdversary
  have h3 := forsOpenPre_le (Lazy.bOpenPreS S.toUnforgeableAdversary)
  rw [← prfAdvantageC_bPrfWC hS.bounds, ← Lazy.prfAdvantage_bPrfMsgWL] at h1
  unfold g2BoundS at h2
  unfold boundFinal
  exact (h1.trans (add_le_add_right h2 _)).trans (compose_le h3)

/-- `slhdsa_suf_cma_final` in the form `∀ S, Adv S ≤ β S`. -/
theorem slhdsa_suf_cma_final' (hS : Structural vp prims) :
    ∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinal S.toUnforgeableAdversary :=
  fun S => slhdsa_suf_cma_final hS S

/-- **Standard-model EUF-CMA security of SLH-DSA (FIPS 205 internal algorithms), final form.**
As `slhdsa_suf_cma_final` for an ordinary chosen-message forger `A` (a forgery is a valid
signature on a message never queried), with the PRF distinguishers `bPrfC A`, `bPrfMsgL A` of
the EUF-CMA check and the same seven other adversaries. -/
theorem slhdsa_euf_cma_final (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinal pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A)) (Lazy.bTcrS A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A)) := by
  have h := slhdsa_euf_cma_v2 hS A
  have h3 := forsOpenPre_le (Lazy.bOpenPreS A)
  unfold boundV2 at h
  unfold boundFinal
  refine h.trans ?_
  gcongr

/-- `slhdsa_euf_cma_final` in the form `∀ A, Adv A ≤ β A` (the shape
`external_bound_of_internal_bound` takes). -/
theorem slhdsa_euf_cma_final' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinal A :=
  fun A => slhdsa_euf_cma_final hS A

/-- EUF-CMA from SUF-CMA: every chosen-message forger is a strong forger (same program), so its
EUF-CMA advantage is also below the SUF-CMA bound `betaSufFinal A`. -/
theorem slhdsa_euf_cma_final_of_suf (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaSufFinal A := by
  let S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist) :=
    ⟨A.main⟩
  have h := slhdsa_suf_cma_final hS S
  rw [SignatureAlg.strongUnforgeableAdvantage_eq_euf_add_sameMessage] at h
  exact le_self_add.trans h

/-! ## External pure interface -/

/-- **Standard-model EUF-CMA security of the external pure interface of SLH-DSA** (FIPS 205
Alg. 21/22/24, messages with context strings), final form.  For every chosen-message forger `A`
against `externalAlg vp prims optRand pkSeedDist` — a forgery is a `(message, context)` pair
never submitted to the signing oracle together with a signature `External.verifyPure` accepts —
the advantage is at most the final bound at the internal forger `toInternal A` (which runs `A`
once and makes at most as many signing queries, `toInternal_queryBound`). -/
theorem slhdsa_pure_euf_cma_final (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinal pkSeedDist (bPrfC (toInternal A)) (Lazy.bPrfMsgL (toInternal A))
        (Lazy.bItsrL (toInternal A))
        (toDspr (Lazy.bOpenPreS (toInternal A))) (toTcr (Lazy.bOpenPreS (toInternal A)))
        (Lazy.bTcrS (toInternal A))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal A))) (rPre pkSeedDist (Lazy.bWotsS (toInternal A)))
        (rTcr pkSeedDist (Lazy.bWotsS (toInternal A))) :=
  external_bound_of_internal_bound betaEufFinal (slhdsa_euf_cma_final' hS) A

/-- **Standard-model SUF-CMA security of the external pure interface of SLH-DSA.**  For every
strong forger `S` against `externalAlg vp prims optRand pkSeedDist` — it wins with a
`((message, context), signature)` pair that `verify` accepts and that the signing oracle never
returned; the error value returned for contexts longer than 255 bytes is never accepted
(`externalAlg_verify_error`) and so is never a forgery — the advantage is at most the final
SUF-CMA bound at the internal forger `toInternal S.toUnforgeableAdversary` (the program of
`toInternalS S`). -/
theorem slhdsa_pure_suf_cma_final (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinal pkSeedDist (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary))
        (Lazy.bItsrL (toInternal S.toUnforgeableAdversary))
        (toDspr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (toTcr (Lazy.bOpenPreS (toInternal S.toUnforgeableAdversary)))
        (Lazy.bTcrS (toInternal S.toUnforgeableAdversary))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rPre pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary)))
        (rTcr pkSeedDist (Lazy.bWotsS (toInternal S.toUnforgeableAdversary))) :=
  (external_strong_advantage_le S).trans (slhdsa_suf_cma_final hS (toInternalS S))

/-! ## Resources -/

/-- The closed-form counts that occur in `FinalResources`. -/
structure Counts where
  /-- PRF queries of the PRF distinguisher; also the fresh draws of each lazy adversary. -/
  secretReads : ℕ
  /-- Hash evaluations (key generation and signing) of each lazy adversary. -/
  hashEvals : ℕ
  /-- Opening queries of the OpenPRE adversary. -/
  openings : ℕ
  /-- FORS leaves of the key structure: commitments / targets of the FORS-leaf games. -/
  forsLeaves : ℕ
  /-- Hash calls of the key structure: targets of SM-TCR(Thash). -/
  thashTargets : ℕ
  /-- WOTS+ instances of the hypertree. -/
  wotsInst : ℕ
  /-- WOTS+ chains: challenges of SM-UD(F) and SM-PRE(F). -/
  wotsChains : ℕ
  /-- WOTS+ chain steps: targets of SM-TCR(F). -/
  wotsSteps : ℕ
  /-- Secret cells of the key structure. -/
  structCells : ℕ

/-- The counts of a parameter set for a forger with at most `qs` signing queries. -/
def counts (vp : ValidatedParams) (qs : ℕ) : Counts where
  secretReads := 2 ^ vp.params.hp * vp.params.len + qs * signReads vp
  hashEvals := Lazy.keygenHashes vp + qs * Lazy.signHashes vp
  openings := qs * vp.params.k
  forsLeaves := openPreTargets vp
  thashTargets := tcrTargets vp
  wotsInst := (wotsInsts vp).length
  wotsChains := (wotsInsts vp).length * vp.params.len
  wotsSteps := (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))
  structCells := openPreTargets vp + (wotsInsts vp).length * vp.params.len

/-- The counts at SLH-DSA-SHA2-128s:
`17920 + qs·182784`, `269824 + qs·2007385`, `14·qs`, `14·2^75 ≈ 2^78.81`, `≈ 2^79.81`,
`≈ 2^63.003`, `≈ 2^68.13`, `≈ 2^72.04`, `≈ 2^78.81`. -/
def counts128s (qs : ℕ) : Counts where
  secretReads := 17920 + qs * 182784
  hashEvals := 269824 + qs * 2007385
  openings := qs * 14
  forsLeaves := 528905046081400263933952
  thashTargets := 1062560399506556770327551
  wotsInst := 9241421688590303744
  wotsChains := 323449759100660631040
  wotsSteps := 4851746386509909465600
  structCells := 529228495840500924564992

theorem counts_128s (qs : ℕ) : counts Link.vp qs = counts128s qs := by
  have h1 : (wotsInsts Link.vp).length * Link.vp.params.len = 323449759100660631040 := by
    rw [← Resources.wotsChainTargets_eq, Resources.wotsChainTargets_128s_val]
  have h2 : Link.vp.params.k = 14 := rfl
  unfold counts counts128s
  rw [Resources.wotsExecutedSteps_128s, h1, Resources.keygenReads_128s, Resources.signReads_128s,
    keygenHashes_128s, signHashes_128s, Resources.openPreTargets_128s_val,
    Resources.tcrTargets_128s_val, Resources.wotsInsts_length_128s, h2]

/-- **Resources of every adversary of the final bounds**, for a forger `A` with at most `qs`
signing queries and the counts `c` (`counts vp qs` in general, `counts128s qs` at SHA2-128s).

Polynomial in `qs`:
* `prf`, `prfSuf` — function queries of the PRF distinguishers `bPrfC A`, `bPrfWC sufCheck A`;
  they draw no secret value;
* `msg*`, `msgSuf*`, `itsr*` — game queries (`≤ qs`), fresh uniform draws (= cache entries) and
  hash evaluations of key generation and signing of the lazy adversaries `bPrfMsgL A`,
  `bPrfMsgWL sufCheck A`, `bItsrL A` (stated on the resource-explicit programs `lazyRes _`, of
  which the adversaries are the interpretation: `Lazy.bPrfMsgL_eq`, `Lazy.bPrfMsgWL_eq`,
  `Lazy.bItsrL_main_eq`);
* `open_find` — opening queries of `bOpenPreS A` (`≤ qs·k`).

Independent of `qs`, whole key structure (`2^68`–`2^80` at SHA2-128s):
* `open_commit`, `open_pick`, `open_samples` — `bOpenPreS A` commits exactly the tweaks of all
  FORS leaves (distinct), makes no collection query, and samples one value per WOTS+ chain;
* `dspr_targets`, `tcrF_targets` — `toDspr B`/`toTcr B` register at most one target per FORS
  leaf, for every OpenPRE adversary `B` (in the bounds: `B = bOpenPreS A`, which commits to
  exactly that many tweaks, so the cap is reached);
* `tcr_choose`, `tcr_targets`, `tcr_samples` — `bTcrS A` registers exactly the hash calls of the
  key structure (distinct tweaks, none refused) and samples one value per secret cell;
* `wots_signed`, `wots_insts`, `wots_samples` — `bWotsS A` requests each WOTS+ instance at most
  once and samples one value per FORS leaf;
* `ud`, `pre`, `tcrW` — challenges/targets of `rUd W`, `rPre W`, `rTcr W` in every run, for
  every WOTS-game adversary `W` (in the bounds: `W = bWotsS A`).

Not counted in this structure: local computation (VCVio has no cost model for it; hash evaluations
are counted here only for the three lazy adversaries; for the SM adversaries after the seed reveal
see `Resources2.FinalResourcesDirect`), the forger's own work, `pkSeedDist`, `optRand`. -/
structure FinalResources (A : Forger vp prims optRand pkSeedDist) (qs : ℕ) (c : Counts) :
    Prop where
  prf : IsQueryBoundP (bPrfC A) (fun i => i.isRight = true) c.secretReads
  prfSuf : IsQueryBoundP (bPrfWC sufCheck A) (fun i => i.isRight = true) c.secretReads
  msg : IsQueryBoundP (Lazy.bPrfMsgL A) (fun i => i.isRight = true) qs
  msg_draws : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpen A)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  msg_hashes : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpen A)) (fun t => Lazy.kind t = .hash)
    c.hashEvals
  msgSuf : IsQueryBoundP (Lazy.bPrfMsgWL sufCheck A) (fun i => i.isRight = true) qs
  msgSuf_draws : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpenW sufCheck A))
    (fun t => Lazy.kind t = .sec) c.secretReads
  msgSuf_hashes : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpenW sufCheck A))
    (fun t => Lazy.kind t = .hash) c.hashEvals
  itsr : IsQueryBoundP (Lazy.bItsrL A).main (fun i => i.isRight = true) qs
  itsr_draws : IsQueryBoundP (Lazy.lazyRes (Lazy.itsrOpen A)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  itsr_hashes : IsQueryBoundP (Lazy.lazyRes (Lazy.itsrOpen A)) (fun t => Lazy.kind t = .hash)
    c.hashEvals
  open_commit : (forsLeafKeys vp prims).Nodup ∧ (forsLeafKeys vp prims).length = c.forsLeaves
  open_pick : IsQueryBoundP (Lazy.bOpenPreS A).pick (fun i => i.isRight = true) 0
  open_find : ∀ st pkSeed ys, IsQueryBoundP ((Lazy.bOpenPreS A).find st pkSeed ys)
    (fun i => i.isRight = true) c.openings
  open_samples : (Lazy.wotsSkIdx vp).length = c.wotsChains
  dspr_targets : ∀ (B : ForsOpenPreAdv vp prims pkSeedDist) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
      (toDspr B).choose).run .initial), z.2.challenges.length ≤ c.forsLeaves
  tcrF_targets : ∀ (B : ForsOpenPreAdv vp prims pkSeedDist) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
      (toTcr B).choose).run .initial), z.2.challenges.length ≤ c.forsLeaves
  tcr_choose : ∀ pk, (simulateQ (SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
      (Lazy.bTcrS A).choose).run ([], []) =
    (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> Lazy.sparseTable vp prims
  tcr_targets : ∀ (tbl : SecretTable vp prims) (pk : prims.PkSeed),
    ((honestCalls tbl pk).map (·.1)).Nodup ∧ (honestCalls tbl pk).length = c.thashTargets
  tcr_samples : (Lazy.structSecIdx vp).length = c.structCells
  wots_signed : ∀ pk, ∀ z ∈ support ((simulateQ (WotsGame.oracles 0 (wotsInsts vp) pk)
      (Lazy.bWotsS A).choose).run ([] : List (WotsGame.Entry prims))),
    (z.2.map (·.1)).Nodup ∧ ∀ a ∈ z.2.map (·.1), a ∈ wotsInsts vp
  wots_insts : (wotsInsts vp).length = c.wotsInst
  wots_samples : (forsSkIdx vp).length = c.forsLeaves
  ud : ∀ (W : WotsGame.Adversary prims) world pk, ∀ z ∈ support ((simulateQ
      (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (rUd pkSeedDist W).pick).run ([], [])), z.2.1.length ≤ c.wotsChains
  pre : ∀ (W : WotsGame.Adversary prims) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
      (rPre pkSeedDist W).choose).run ([], [])), z.2.1.length ≤ c.wotsChains
  tcrW : ∀ (W : WotsGame.Adversary prims) pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (rTcr pkSeedDist W).choose).run ([], [])), z.2.1.length ≤ c.wotsSteps

/-- Each projection of `counts`, as a rewriting lemma (so that no proof below has to unify a
closed form with a projection of `counts vp qs` by unfolding the closed form). -/
theorem counts_eq (vp : ValidatedParams) (qs : ℕ) :
    (counts vp qs).secretReads = 2 ^ vp.params.hp * vp.params.len + qs * signReads vp ∧
    (counts vp qs).hashEvals = Lazy.keygenHashes vp + qs * Lazy.signHashes vp ∧
    (counts vp qs).openings = qs * vp.params.k ∧
    (counts vp qs).forsLeaves = openPreTargets vp ∧
    (counts vp qs).thashTargets = tcrTargets vp ∧
    (counts vp qs).wotsInst = (wotsInsts vp).length ∧
    (counts vp qs).wotsChains = (wotsInsts vp).length * vp.params.len ∧
    (counts vp qs).wotsSteps = (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)) ∧
    (counts vp qs).structCells = openPreTargets vp + (wotsInsts vp).length * vp.params.len := by
  unfold counts
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The resource theorem.**  Every count of `FinalResources` holds with the closed forms
`counts vp qs`, for every forger with at most `qs` signing queries. -/
theorem final_resources (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResources A qs (counts vp qs) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := counts_eq vp qs
  generalize counts vp qs = c at e1 e2 e3 e4 e5 e6 e7 e8 e9 ⊢
  refine
    { prf := e1 ▸ bPrfC_queryBound_exact A qs hA
      prfSuf := e1 ▸ bPrfWC_queryBound_exact sufCheck A qs hA
      msg := Lazy.bPrfMsgL_queryBound A qs hA
      msg_draws := e1 ▸ Lazy.bPrfMsgL_draws A qs hA
      msg_hashes := e2 ▸ Lazy.bPrfMsgL_hashes A qs hA
      msgSuf := Lazy.bPrfMsgWL_queryBound sufCheck A qs hA
      msgSuf_draws := e1 ▸ Lazy.bPrfMsgWL_draws sufCheck A qs hA
      msgSuf_hashes := e2 ▸ Lazy.bPrfMsgWL_hashes sufCheck A qs hA
      itsr := Lazy.bItsrL_queryBound A qs hA
      itsr_draws := e1 ▸ Lazy.bItsrL_draws A qs hA
      itsr_hashes := e2 ▸ Lazy.bItsrL_hashes A qs hA
      open_commit := e4 ▸ Lazy.bOpenPreS_targets hS
      open_pick := Lazy.bOpenPreS_pick_queryBound A
      open_find := fun st pkSeed ys => e3 ▸ Lazy.bOpenPreS_find_queryBound A qs hA st pkSeed ys
      open_samples := e7 ▸ Lazy.wotsSkIdx_length
      dspr_targets := ?_
      tcrF_targets := ?_
      tcr_choose := fun pk => Lazy.bTcrS_choose_run hS A pk
      tcr_targets := fun tbl pk => e5 ▸ Lazy.bTcrS_targets hS tbl pk
      tcr_samples := ?_
      wots_signed := fun pk => Lazy.bWotsS_choose_signed A pk
      wots_insts := e6.symm
      wots_samples := ?_
      ud := fun W world pk z hz =>
        e7 ▸ (Resources.rUd_challenges_le pkSeedDist hS world W pk z hz).2
      pre := fun W pk z hz =>
        e7 ▸ (Resources.rPre_challenges_le pkSeedDist hS W pk z hz).2.2
      tcrW := fun W pk z hz =>
        e8 ▸ (Resources.rTcr_targets_le pkSeedDist hS W pk z hz).2.2 }
  · intro B pk z hz
    rw [e4]
    have h := toDspr_targets B pk z hz
    exact h.elim fun _ h' => h'.2.2.1
  · intro B pk z hz
    rw [e4]
    have h := toTcr_targets B pk z hz
    exact h.elim fun _ h' => h'.2.2.1
  · rw [e9, Lazy.structSecIdx_length, ← Resources.openPreTargets_eq_length]
  · rw [e4, Lazy.bWotsS_sampleCount, ← Resources.openPreTargets_eq_length]

/-- **SUF-CMA bound and resources together**, for a strong forger with at most `qs` signing
queries. -/
theorem slhdsa_suf_cma_final_resources (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist))
    (qs : ℕ) (hq : ∀ pk, IsQueryBoundP (S.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinal S.toUnforgeableAdversary ∧
      FinalResources S.toUnforgeableAdversary qs (counts vp qs) :=
  ⟨slhdsa_suf_cma_final hS S, final_resources hS S.toUnforgeableAdversary qs hq⟩

/-- **External SUF-CMA bound and resources together**: if the external strong forger makes at
most `qs` signing queries, so does `toInternal S.toUnforgeableAdversary`, and the counts hold
for the adversaries built from it. -/
theorem slhdsa_pure_suf_cma_final_resources (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist)
    (qs : ℕ) (hq : ∀ pk, IsQueryBoundP (S.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinal (toInternal S.toUnforgeableAdversary) ∧
      FinalResources (toInternal S.toUnforgeableAdversary) qs (counts vp qs) :=
  ⟨slhdsa_pure_suf_cma_final hS S,
    final_resources hS _ qs (toInternal_queryBound S.toUnforgeableAdversary qs hq)⟩

/-- **External EUF-CMA bound and resources together.** -/
theorem slhdsa_pure_euf_cma_final_resources (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist)
    (qs : ℕ) (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinal (toInternal A) ∧
      FinalResources (toInternal A) qs (counts vp qs) :=
  ⟨slhdsa_pure_euf_cma_final hS A, final_resources hS _ qs (toInternal_queryBound A qs hq)⟩

end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction

open TweakableHash

/-- **SUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms) in the standard model.**
No hypothesis besides the strong forger. -/
theorem slhdsa_sha2_128s_suf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinal pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (Lazy.bTcrS S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcr pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) :=
  slhdsa_suf_cma_final structural_128s S

/-- **EUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms) in the standard model.** -/
theorem slhdsa_sha2_128s_euf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinal pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A)) (Lazy.bTcrS A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A)) :=
  slhdsa_euf_cma_final structural_128s A

/-- **EUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : ExtForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinal (toInternal A) :=
  slhdsa_pure_euf_cma_final structural_128s A

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : ExtStrongForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinal (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final structural_128s S

/-- **Resources at SLH-DSA-SHA2-128s, as numerals**: for a forger with at most `qs` signing
queries, `FinalResources A qs (counts128s qs)`:

* PRF: `≤ 17920 + qs·182784` queries; PRF_msg, ITSR: `≤ qs` game queries,
  `≤ 17920 + qs·182784` fresh draws, `≤ 269824 + qs·2007385` hash evaluations;
* OpenPRE adversary: `528905046081400263933952 = 14·2^75 ≈ 2^78.81` commitments, `≤ 14·qs`
  openings, `323449759100660631040 ≈ 2^68.13` samples; SM-DSPR(F), SM-TCR(F) at FORS leaves:
  `≤ 14·2^75` targets;
* SM-TCR(Thash): `1062560399506556770327551 ≈ 2^79.81` targets,
  `529228495840500924564992 ≈ 2^78.81` samples;
* WOTS game: `≤ 9241421688590303744 ≈ 2^63.003` signed instances, `14·2^75` samples;
  SM-UD(F), SM-PRE(F): `≤ 323449759100660631040 ≈ 2^68.13` challenges; SM-TCR(F):
  `≤ 4851746386509909465600 ≈ 2^72.04` targets. -/
theorem final_resources_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResources A qs (counts128s qs) :=
  counts_128s qs ▸ final_resources structural_128s A qs hA

#print axioms slhdsa_suf_cma_final
#print axioms slhdsa_euf_cma_final
#print axioms slhdsa_euf_cma_final_of_suf
#print axioms slhdsa_pure_euf_cma_final
#print axioms slhdsa_pure_suf_cma_final
#print axioms final_resources
#print axioms slhdsa_suf_cma_final_resources
#print axioms slhdsa_pure_suf_cma_final_resources
#print axioms slhdsa_pure_euf_cma_final_resources
#print axioms slhdsa_sha2_128s_suf_cma_final
#print axioms slhdsa_sha2_128s_euf_cma_final
#print axioms slhdsa_sha2_128s_pure_euf_cma_final
#print axioms slhdsa_sha2_128s_pure_suf_cma_final
#print axioms final_resources_128s

end Reduction
