import Reduction.Resources2Tcr
import Reduction.Resources2Fors

/-!
# Direct resource lemmas for the adversaries of the headline bounds (package W3)

Every statement here is about the headline adversary TERM itself: either a property of every
element of the support of the run of its phase-1 program against the oracles of its game, or an
equation exhibiting that run (which shows the fresh uniform samples as an explicit
`Tables.sampleList prims.Y n` / `ForsTight.sampleT ($ᵗ prims.Y) keys`), or a query bound
(`IsQueryBoundP`) of the term / of the open program of which its phase-2 program is the
interpretation.  `status/W3.md` has the table.

## Phase 1 (seed hidden) — this file

* `toDspr (Lazy.bOpenPreS A)`, `toTcr (Lazy.bOpenPreS A)`:
  `forsTcr_choose_run`, `forsDspr_choose_run` (run in closed form: `#inst·len` samples for the
  WOTS+ cells, then one uniform input per FORS leaf), `forsTcr_targets`, `forsDspr_targets`
  (in every run: target tweaks are exactly `forsLeafKeys`, `2^h·k·2^a` targets, NO collection
  query).
* `bTcrArS n A`: `bTcrArS_choose_run_samples` (run in closed form: `2^h·k·2^a + #inst·len`
  samples), `bTcrArS_phase1` (in every run: exactly `arityTargets vp n` targets and
  `tcrTargets vp - arityTargets vp n` collection queries).
* `rUd/rPre/rTcr pkSeedDist (Lazy.bWotsS A)`: `rUd_bWotsS_challenges`, `rPre_bWotsS_challenges`,
  `rTcr_bWotsS_targets` (in every run: `≤ #inst·len`, `≤ #inst·len`, `≤ #inst·len·(w-1)`
  accepted challenges/targets), instances of the generic lemmas of `Reduction.Resources`.

NOT formal for the three WOTS adversaries (counting arguments, see `Reduction/Resources.lean`
module doc and `Lazy/WotsSparse.lean`): their collection queries
(`rUd`, `rPre`: `≤ qc + #inst·len·(w-1)`; `rTcr`: `≤ qc + #inst·len`, with
`qc = 2^h·(k·(2^(a+1)-1)+1) + (#trees+1)·(2^(h'+1)-1)` the collection queries of `bWotsS A`),
and their own fresh samples (`bWotsS A`: exactly `2^h·k·2^a` values, formal:
`Lazy.bWotsS_choose_eq`; the wrappers: `≤ #inst·len` values of `Y`, and one hybrid index for
`rUd`).

## Phase 2 (seed revealed) — `Resources2Fors`, `Resources2Tcr`, `Resources2Wots`

## Bundle

`FinalResourcesDirect`, `final_resources_direct`, `final_resources_direct_128s`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Resources2

open TweakableHash

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## SM-DSPR(F), SM-TCR(F) at the FORS leaves: phase 1 -/

section Fors

open SM_DT_OpenPRE_SourceFinalValidity

/-- The commitment phase of `bOpenPreWith my A` inside its game: the table is drawn, the
committed tweaks are `forsLeafKeys`, the game state is untouched (no collection query). -/
theorem fors_pick_run (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (pickOracles (forsOpenPreProblem vp prims pkSeedDist) pk)
        (bOpenPreWith my A).pick).run .initial =
      my >>= fun tbl => pure ((tbl, forsLeafKeys vp prims), .initial) := by
  simp [bOpenPreWith, pickOracles, QueryImpl.simulateQ_add_liftM_left]

theorem fors_take_keys (hS : Structural vp prims) :
    (forsLeafKeys vp prims).take (openPreTargets vp) = forsLeafKeys vp prims :=
  List.take_of_length_le (Lazy.bOpenPreS_targets hS).2.le

/-- Recording targets never touches the collection record. -/
theorem fors_recAll_collectionTweaks {Tweak M : Type} [DecidableEq Tweak] (n : ℕ)
    (st : SourceFinalValidity.State (Tweak × M) Tweak) (tg : List (Tweak × M)) :
    (ForsTight.recAll n st tg).collectionTweaks = st.collectionTweaks := by
  induction tg generalizing st with
  | nil => rfl
  | cons q tg ih => rw [ForsTight.recAll_cons, ih]; rfl

/-- **Phase 1 of `toTcr (bOpenPreWith my A)` in its game, in closed form**: the table sampler,
then one uniform input per FORS leaf tweak; nothing else is sampled and nothing is queried
besides these targets. -/
theorem forsTcrWith_choose_run (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
        (toTcr (bOpenPreWith my A)).choose).run .initial =
      my >>= fun tbl => ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
        pure ((tbl, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
          ForsTight.recAll (openPreTargets vp) .initial tg) := by
  rw [toTcr_choose_run, fors_pick_run]
  refine (bind_assoc _ _ _).trans (bind_congr fun tbl => (pure_bind _ _).trans ?_)
  exact congrArg (fun ks => ForsTight.sampleT ($ᵗ prims.Y) ks >>= fun tg =>
    (pure ((tbl, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
      ForsTight.recAll (openPreTargets vp) .initial tg) : ProbComp _)) (fors_take_keys hS)

theorem forsDsprWith_choose_run (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
        (toDspr (bOpenPreWith my A)).choose).run .initial =
      my >>= fun tbl => ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
        pure ((tbl, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
          ForsTight.recAll (openPreTargets vp) .initial tg) := by
  rw [toDspr_choose_run, fors_pick_run]
  refine (bind_assoc _ _ _).trans (bind_congr fun tbl => (pure_bind _ _).trans ?_)
  exact congrArg (fun ks => ForsTight.sampleT ($ᵗ prims.Y) ks >>= fun tg =>
    (pure ((tbl, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
      ForsTight.recAll (openPreTargets vp) .initial tg) : ProbComp _)) (fors_take_keys hS)

/-- What every outcome of the closed-form phase-1 run satisfies. -/
theorem fors_run_support (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (pk : prims.PkSeed) :
    ∀ z ∈ support (my >>= fun tbl =>
        ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
        (pure ((tbl, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
          ForsTight.recAll (openPreTargets vp) .initial tg) :
          ProbComp ((SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y) ×
            SourceFinalValidity.State (prims.AdrsKey × prims.Y) prims.AdrsKey))),
      z.2.challenges.map Prod.fst = forsLeafKeys vp prims ∧
        z.2.challenges.length = openPreTargets vp ∧ z.2.collectionTweaks = [] := by
  intro z hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨tbl, -, tg, htg, rfl⟩ := hz
  have hfst := ForsTight.sampleT_fst _ _ tg htg
  have hc : (ForsTight.recAll (openPreTargets vp)
      (SourceFinalValidity.State.initial : SourceFinalValidity.State (prims.AdrsKey × prims.Y)
        prims.AdrsKey) tg).challenges = tg := by
    rw [ForsTight.recAll_challenges]; rfl
  refine ⟨by rw [hc, hfst], ?_, ?_⟩
  · rw [hc, ← List.length_map (f := Prod.fst), hfst]
    exact (Lazy.bOpenPreS_targets hS).2
  · rw [fors_recAll_collectionTweaks]; rfl

/-- **Phase 1 of `toTcr (bOpenPreS A)`, closed form**: `(wotsSkIdx vp).length = #inst·len`
uniform values (the WOTS+ start cells of the sparse table), then one uniform input per FORS leaf
(`(forsLeafKeys vp prims).length = 2^h·k·2^a`). -/
theorem forsTcr_choose_run (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
        (toTcr (Lazy.bOpenPreS A)).choose).run .initial =
      Tables.sampleList prims.Y (Lazy.wotsSkIdx vp).length >>= fun ws =>
        ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
        pure ((Tables.updateList (fun _ => default) (Lazy.wotsSkIdx vp) ws, tg,
            ForsTight.images (fHash vp prims pkSeedDist) pk tg),
          ForsTight.recAll (openPreTargets vp) .initial tg) :=
  (forsTcrWith_choose_run hS (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A pk).trans
    (bind_map_left _ _ _)

theorem forsDspr_choose_run (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
        (toDspr (Lazy.bOpenPreS A)).choose).run .initial =
      Tables.sampleList prims.Y (Lazy.wotsSkIdx vp).length >>= fun ws =>
        ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
        pure ((Tables.updateList (fun _ => default) (Lazy.wotsSkIdx vp) ws, tg,
            ForsTight.images (fHash vp prims pkSeedDist) pk tg),
          ForsTight.recAll (openPreTargets vp) .initial tg) :=
  (forsDsprWith_choose_run hS (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A pk).trans
    (bind_map_left _ _ _)

/-- **Targets of `toTcr (bOpenPreS A)`**: in every run of phase 1 in the SM-TCR(F) game the
target tweaks are exactly the FORS leaf tweaks, there are exactly `openPreTargets vp` targets,
and no collection query was made. -/
theorem forsTcr_targets (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ
        (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
        (toTcr (Lazy.bOpenPreS A)).choose).run .initial),
      z.2.challenges.map Prod.fst = forsLeafKeys vp prims ∧
        z.2.challenges.length = openPreTargets vp ∧ z.2.collectionTweaks = [] := by
  intro z hz
  have h := forsTcrWith_choose_run hS (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A pk
  exact fors_run_support hS _ pk z (h ▸ hz)

/-- **Targets of `toDspr (bOpenPreS A)`**: as for `toTcr (bOpenPreS A)`. -/
theorem forsDspr_targets (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ
        (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
        (toDspr (Lazy.bOpenPreS A)).choose).run .initial),
      z.2.challenges.map Prod.fst = forsLeafKeys vp prims ∧
        z.2.challenges.length = openPreTargets vp ∧ z.2.collectionTweaks = [] := by
  intro z hz
  have h := forsDsprWith_choose_run hS (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A pk
  exact fors_run_support hS _ pk z (h ▸ hz)

end Fors

/-! ## The four arity-class SM-TCR games: phase 1 -/

/-- **Phase 1 of `bTcrArS n A`, closed form**: `(structSecIdx vp).length` uniform values, then a
deterministic walk whose recorded game state is `gState` of the honest calls. -/
theorem bTcrArS_choose_run_samples (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArS n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          ((fun xs => Tables.updateList (fun _ => default) (Lazy.structSecIdx vp) xs) <$>
            Tables.sampleList prims.Y (Lazy.structSecIdx vp).length) := by
  rw [bTcrArS_choose_run hS, Lazy.sparseTable_eq]

/-- In every run of phase 1 of the SM-TCR adversary `B` in its game (every seed), exactly `nT`
targets have been accepted, and accepted targets plus recorded collection queries are `nAll`.
(A predicate generic in `B`, for the reason explained at `UdChallengesLe` below.) -/
def TcrPhase1Counts {ι' PkSeed Tweak M Y : Type} [DecidableEq Tweak]
    {prob : SM_DT_TCR_Problem ι' PkSeed Tweak M Y} (B : SM_DT_TCR_Adversary prob)
    (nT nAll : ℕ) : Prop :=
  ∀ pk : PkSeed, ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles prob pk) B.choose).run ([], [])),
    z.2.1.length = nT ∧ z.2.1.length + z.2.2.length = nAll

theorem tcrPhase1Counts_of_run {ι' PkSeed Tweak M Y : Type} [DecidableEq Tweak]
    {prob : SM_DT_TCR_Problem ι' PkSeed Tweak M Y} (B : SM_DT_TCR_Adversary prob)
    (nT nAll : ℕ) {T : Type} (my : ProbComp T)
    (g : PkSeed → T → B.State × SM_DT_TCR_State Tweak M)
    (hrun : ∀ pk, (simulateQ (SM_DT_TCR_oracles prob pk) B.choose).run ([], []) = g pk <$> my)
    (hg : ∀ pk t, (g pk t).2.1.length = nT ∧ (g pk t).2.1.length + (g pk t).2.2.length = nAll) :
    TcrPhase1Counts B nT nAll := by
  intro pk z hz
  rw [hrun pk, support_map] at hz
  obtain ⟨t, -, rfl⟩ := hz
  exact hg pk t

/-- **Targets and collection queries of `bTcrArS n A`**: in every run of phase 1 in the class-`n`
SM-TCR game, exactly `arityTargets vp n` targets are registered, and the targets and collection
queries together are the `tcrTargets vp` hash calls of the key structure (so exactly
`tcrTargets vp - arityTargets vp n` collection queries). -/
theorem bTcrArS_phase1 (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    TcrPhase1Counts (bTcrArS n A) (arityTargets vp n) (tcrTargets vp) :=
  tcrPhase1Counts_of_run _ _ _ (Lazy.sparseTable vp prims)
    (fun pk tbl => ((tbl, honestCalls tbl pk),
      TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)))
    (fun pk => bTcrArS_choose_run hS n A pk)
    (fun pk tbl => ⟨(bTcrArS_targets hS n tbl pk).1, (bTcrArS_targets hS n tbl pk).2.1⟩)

/-! ## SM-UD(F), SM-PRE(F), SM-TCR(F) on chains: phase 1

The statements are phrased through predicates that are generic in the WOTS-game adversary `W`
(`UdChallengesLe`, `PreChallengesLe`, `WTcrTargetsLe`): elaborating the unfolded statement at
the concrete term `Lazy.bWotsS A` exceeds the default heartbeat limit (`whnf`), whereas
`P (Lazy.bWotsS A)` with `P` a definition is checked without unfolding.  Unfold the predicate
(`Iff.rfl` / `unfold`) to read the statement. -/

/-- In every run of phase 1 of `rUd pkSeedDist W` in the SM-UD game (both worlds, every seed),
the game has accepted at most `n` challenges. -/
def UdChallengesLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) (n : ℕ) :
    Prop :=
  ∀ (world : SM_DT_UD_World) (pk : prims.PkSeed),
    ∀ z ∈ support ((simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (rUd pkSeedDist W).pick).run ([], [])), z.2.1.length ≤ n

/-- In every run of phase 1 of `rPre pkSeedDist W` in the SM-PRE game, the game has accepted at
most `n` challenges. -/
def PreChallengesLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) (n : ℕ) :
    Prop :=
  ∀ pk : prims.PkSeed,
    ∀ z ∈ support ((simulateQ (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
      (rPre pkSeedDist W).choose).run ([], [])), z.2.1.length ≤ n

/-- In every run of phase 1 of `rTcr pkSeedDist W` in the SM-TCR game on chains, the game has
accepted at most `n` targets. -/
def WTcrTargetsLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) (n : ℕ) :
    Prop :=
  ∀ pk : prims.PkSeed,
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (rTcr pkSeedDist W).choose).run ([], [])), z.2.1.length ≤ n

theorem udChallengesLe_of (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    UdChallengesLe pkSeedDist W ((wotsInsts vp).length * vp.params.len) :=
  fun world pk z hz => (Resources.rUd_challenges_le pkSeedDist hS world W pk z hz).2

theorem preChallengesLe_of (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    PreChallengesLe pkSeedDist W ((wotsInsts vp).length * vp.params.len) :=
  fun pk z hz => (Resources.rPre_challenges_le pkSeedDist hS W pk z hz).2.2

theorem wTcrTargetsLe_of (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    WTcrTargetsLe pkSeedDist W ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) :=
  fun pk z hz => (Resources.rTcr_targets_le pkSeedDist hS W pk z hz).2.2

/-- **Challenges of `rUd pkSeedDist (bWotsS A)`**: at most `#inst·len` in every run (both
worlds). -/
theorem rUd_bWotsS_challenges (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    UdChallengesLe pkSeedDist (Lazy.bWotsS A) ((wotsInsts vp).length * vp.params.len) :=
  udChallengesLe_of hS _

/-- **Challenges of `rPre pkSeedDist (bWotsS A)`**: at most `#inst·len` in every run. -/
theorem rPre_bWotsS_challenges (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    PreChallengesLe pkSeedDist (Lazy.bWotsS A) ((wotsInsts vp).length * vp.params.len) :=
  preChallengesLe_of hS _

/-- **Targets of `rTcr pkSeedDist (bWotsS A)`**: at most `#inst·len·(w-1)` in every run. -/
theorem rTcr_bWotsS_targets (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    WTcrTargetsLe pkSeedDist (Lazy.bWotsS A)
      ((wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) :=
  wTcrTargetsLe_of hS _

#print axioms forsTcr_choose_run
#print axioms forsDspr_choose_run
#print axioms forsTcr_targets
#print axioms forsDspr_targets
#print axioms bTcrArS_choose_run_samples
#print axioms bTcrArS_phase1
#print axioms rUd_bWotsS_challenges
#print axioms rPre_bWotsS_challenges
#print axioms rTcr_bWotsS_targets

end Resources2
end Reduction

/-! ## The bundle -/

namespace Reduction
namespace Resources2

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The closed forms occurring in `FinalResourcesDirect`. -/
structure DirectCounts where
  /-- PRF queries of the PRF distinguishers; fresh draws of each lazy adversary. -/
  secretReads : ℕ
  /-- Hash evaluations (key generation and signing) of each lazy adversary. -/
  lazyHashes : ℕ
  /-- Opening queries simulated in phase 2 of the FORS-leaf adversaries. -/
  openings : ℕ
  /-- FORS leaves: targets of SM-DSPR(F), SM-TCR(F); samples of `bWotsS`. -/
  forsLeaves : ℕ
  /-- WOTS+ chains: challenges of SM-UD/SM-PRE; table samples of the FORS-leaf adversaries. -/
  wotsChains : ℕ
  /-- WOTS+ chain steps: targets of SM-TCR(F) on chains. -/
  wotsSteps : ℕ
  /-- All hash calls of the key structure: targets + collection queries of each class game, and
  the exact size of the phase-2 structure recomputation of `bTcrArS n A`. -/
  thashTargets : ℕ
  /-- Secret cells of the key structure: samples of `bTcrArS n A`. -/
  structCells : ℕ
  /-- Targets of the class games `F`, `H`, `T_len`, `T_k`. -/
  arF : ℕ
  arH : ℕ
  arLen : ℕ
  arK : ℕ
  /-- Own phase-2 hash evaluations of `toDspr`/`toTcr (bOpenPreS A)`. -/
  forsP2 : ℕ
  /-- Own phase-2 hash evaluations of `bTcrArS n A` (without the final collision search). -/
  tcrP2 : ℕ
  /-- Own phase-2 hash evaluations of `rUd`/`rPre`/`rTcr` at `bWotsS A` (without `wotsAnswer`). -/
  udP2 : ℕ
  preP2 : ℕ
  wtcrP2 : ℕ

/-- The counts of a parameter set for a forger with at most `qs` signing queries. -/
def directCounts (vp : ValidatedParams) (qs : ℕ) : DirectCounts where
  secretReads := 2 ^ vp.params.hp * vp.params.len + qs * signReads vp
  lazyHashes := Lazy.keygenHashes vp + qs * Lazy.signHashes vp
  openings := qs * vp.params.k
  forsLeaves := openPreTargets vp
  wotsChains := (wotsInsts vp).length * vp.params.len
  wotsSteps := (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))
  thashTargets := tcrTargets vp
  structCells := openPreTargets vp + (wotsInsts vp).length * vp.params.len
  arF := arityTargets vp 1
  arH := arityTargets vp 2
  arLen := arityTargets vp vp.params.len
  arK := arityTargets vp vp.params.k
  forsP2 := Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)
  tcrP2 := Lazy.keygenHashes vp + qs * Lazy.signHashes vp + tcrTargets vp
  udP2 := qs * wotsSignHistHashes vp + wotsWinHashes vp
  preP2 := qs * wotsSignHistHashes vp + wotsPreHashes vp
  wtcrP2 := qs * wotsSignHistHashes vp + wotsTcrHashes vp

/-- The counts at SLH-DSA-SHA2-128s. -/
def directCounts128s (qs : ℕ) : DirectCounts where
  secretReads := 17920 + qs * 182784
  lazyHashes := 269824 + qs * 2007385
  openings := qs * 14
  forsLeaves := 528905046081400263933952
  wotsChains := 323449759100660631040
  wotsSteps := 4851746386509909465600
  thashTargets := 1062560399506556770327551
  structCells := 529228495840500924564992
  arF := 533756792467910173399552
  arH := 528785142244921151848447
  arLen := 9241421688590303744
  arK := 9223372036854775808
  forsP2 := 269824 + qs * 1950027 + (1 + qs + 14)
  tcrP2 := 269824 + qs * 2007385 + 1062560399506556770327551
  udP2 := qs * 121857 + 525
  preP2 := qs * 121857 + 560
  wtcrP2 := qs * 121857 + 16800

/-- **Direct resources of every adversary of the headline bounds** (`boundFinalSplit`), for a
forger `A` with at most `qs` signing queries.  Every field is a statement about the adversary
term itself.  Notation: "run" = run of the phase-1 program against the oracles of its game from
the initial game state, for every seed `pk`; "open program" = `OracleComp (Lazy.OSpec prims _)`,
in which every evaluation of `Thash`/`Hmsg` is a query of kind `.hash`, interpreted by
`Lazy.tblImpl (PublicHash.impl prims) tbl` (hash queries by `prims`, secret reads from the
adversary's table).

* `prf` … `itsr_hashes`: PRF / PRF_msg / ITSR adversaries (queries, fresh draws, hash
  evaluations; poly(`qs`)).
* `fors_*`: `toDspr (bOpenPreS A)`, `toTcr (bOpenPreS A)`.  Phase 1: run in closed form
  (`wotsChains` table samples, then one uniform input per FORS leaf), exactly `forsLeaves`
  targets with the FORS-leaf tweaks, no collection query.  Phase 2: one run of the open program
  `findOpenFull A pk ys` under the local opening simulation; `≤ forsP2` hash evaluations,
  `≤ openings` simulated openings.
* `tcr_*`: `bTcrArS n A` (`n = 1, 2, len, k`).  Phase 1: run in closed form (`structCells`
  samples), exactly `arityTargets vp n` targets and `thashTargets - arityTargets vp n`
  collection queries.  Phase 2: the open program `tcrForgeOpen A tbl pk` (then a hash-free index
  translation), `≤ tcrP2` hash evaluations, of which the recomputation of the whole key
  structure accounts for exactly `thashTargets` (`tcr_phase2_exact`).
* `ud_*`, `pre_*`, `wtcr_*`: `rUd/rPre/rTcr pkSeedDist (bWotsS A)`.  Phase 1: `≤ wotsChains`,
  `≤ wotsChains`, `≤ wotsSteps` accepted challenges/targets in every run; `wots_choose`: the
  inner adversary draws exactly `forsLeaves` uniform values.  Phase 2: the open program
  `wotsPhase2O …`, `≤ udP2 / preP2 / wtcrP2` hash evaluations.

Not in the bundle (counting arguments only; `status/W3.md`): collection queries and own samples
of `rUd/rPre/rTcr`; the pure tails `findCollision`/`verifyCalls` (TCR) and `wotsAnswer` (WOTS);
absence of local hashing in phase 1. -/
structure FinalResourcesDirect (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (c : DirectCounts) : Prop where
  prf : IsQueryBoundP (bPrfC A) (fun i => i.isRight = true) c.secretReads
  prfSuf : IsQueryBoundP (bPrfWC sufCheck A) (fun i => i.isRight = true) c.secretReads
  msg : IsQueryBoundP (Lazy.bPrfMsgL A) (fun i => i.isRight = true) qs
  msg_draws : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpen A)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  msg_hashes : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpen A)) (fun t => Lazy.kind t = .hash)
    c.lazyHashes
  msgSuf : IsQueryBoundP (Lazy.bPrfMsgWL sufCheck A) (fun i => i.isRight = true) qs
  msgSuf_draws : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpenW sufCheck A))
    (fun t => Lazy.kind t = .sec) c.secretReads
  msgSuf_hashes : IsQueryBoundP (Lazy.lazyRes (Lazy.msgOpenW sufCheck A))
    (fun t => Lazy.kind t = .hash) c.lazyHashes
  itsr : IsQueryBoundP (Lazy.bItsrL A).main (fun i => i.isRight = true) qs
  itsr_draws : IsQueryBoundP (Lazy.lazyRes (Lazy.itsrOpen A)) (fun t => Lazy.kind t = .sec)
    c.secretReads
  itsr_hashes : IsQueryBoundP (Lazy.lazyRes (Lazy.itsrOpen A)) (fun t => Lazy.kind t = .hash)
    c.lazyHashes
  fors_tcr_run : ∀ pk, (simulateQ
      (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
      (toTcr (Lazy.bOpenPreS A)).choose).run .initial =
    Tables.sampleList prims.Y (Lazy.wotsSkIdx vp).length >>= fun ws =>
      ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
      pure ((Tables.updateList (fun _ => default) (Lazy.wotsSkIdx vp) ws, tg,
          ForsTight.images (fHash vp prims pkSeedDist) pk tg),
        ForsTight.recAll (openPreTargets vp) .initial tg)
  fors_dspr_run : ∀ pk, (simulateQ
      (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
      (toDspr (Lazy.bOpenPreS A)).choose).run .initial =
    Tables.sampleList prims.Y (Lazy.wotsSkIdx vp).length >>= fun ws =>
      ForsTight.sampleT ($ᵗ prims.Y) (forsLeafKeys vp prims) >>= fun tg =>
      pure ((Tables.updateList (fun _ => default) (Lazy.wotsSkIdx vp) ws, tg,
          ForsTight.images (fHash vp prims pkSeedDist) pk tg),
        ForsTight.recAll (openPreTargets vp) .initial tg)
  fors_tcr_targets : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
      (toTcr (Lazy.bOpenPreS A)).choose).run .initial),
    z.2.challenges.map Prod.fst = forsLeafKeys vp prims ∧
      z.2.challenges.length = c.forsLeaves ∧ z.2.collectionTweaks = []
  fors_dspr_targets : ∀ pk, ∀ z ∈ support ((simulateQ
      (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
      (toDspr (Lazy.bOpenPreS A)).choose).run .initial),
    z.2.challenges.map Prod.fst = forsLeafKeys vp prims ∧
      z.2.challenges.length = c.forsLeaves ∧ z.2.collectionTweaks = []
  fors_samples : (Lazy.wotsSkIdx vp).length = c.wotsChains ∧
    (forsLeafKeys vp prims).length = c.forsLeaves
  fors_tcr_phase2 : ∀ (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
      (ys : List prims.Y) (pk : prims.PkSeed),
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      (simulateQ (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFull A pk ys))).run [] >>= fun z => pure z.1
  fors_dspr_phase2 : ∀ (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
      (ys : List prims.Y) (pk : prims.PkSeed),
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      (simulateQ (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFull A pk ys))).run [] >>= fun z => pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2))
  fors_phase2_hashes : ∀ pk ys, IsQueryBoundP (findOpenFull A pk ys)
    (fun t => Lazy.kind t = .hash) c.forsP2
  fors_phase2_openings : ∀ pk ys, IsQueryBoundP (findOpenFull A pk ys)
    (fun t => Lazy.kind t = .game) c.openings
  tcr_run : ∀ n pk, (simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
      (bTcrArS n A).choose).run ([], []) =
    (fun tbl => ((tbl, honestCalls tbl pk),
      TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
        ((fun xs => Tables.updateList (fun _ => default) (Lazy.structSecIdx vp) xs) <$>
          Tables.sampleList prims.Y (Lazy.structSecIdx vp).length)
  tcr_phase1 : ∀ n, TcrPhase1Counts (bTcrArS n A) (arityTargets vp n) c.thashTargets
  tcr_arity : arityTargets vp 1 = c.arF ∧ arityTargets vp 2 = c.arH ∧
    arityTargets vp vp.params.len = c.arLen ∧ arityTargets vp vp.params.k = c.arK
  tcr_samples : (Lazy.structSecIdx vp).length = c.structCells
  tcr_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (n : ℕ) (tbl : SecretTable vp prims)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    (liftM ((bTcrArS n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (tcrForgeOpen A tbl pk) >>= fun jm =>
        pure (match L[jm.1]? with
          | some q => if h : q.2.length = n ∧ jm.2.length = n then
              (TcrSplit.classIdx (fun xs : List prims.Y => xs.length = n) L jm.1, ⟨jm.2, h.2⟩)
              else (L.length, arityDefault prims n)
          | none => (L.length, arityDefault prims n))
  tcr_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (pk : prims.PkSeed),
    IsQueryBoundP (tcrForgeOpen (gspec := gspec) A tbl pk) (fun t => Lazy.kind t = .hash) c.tcrP2
  tcr_phase2_exact : ∀ (tbl : SecretTable vp prims) (pk : prims.PkSeed),
    honestCalls tbl pk = ((simulateQ (logImpl pk) (structureFree tbl)).run []).2 ∧
      (honestCalls tbl pk).length = c.thashTargets
  ud_phase1 : UdChallengesLe pkSeedDist (Lazy.bWotsS A) c.wotsChains
  pre_phase1 : PreChallengesLe pkSeedDist (Lazy.bWotsS A) c.wotsChains
  wtcr_phase1 : WTcrTargetsLe pkSeedDist (Lazy.bWotsS A) c.wotsSteps
  wots_choose : (Lazy.bWotsS A).choose =
    (monadLift (Tables.sampleList prims.Y (forsSkIdx vp).length) :
      OracleComp (WSpec prims) (List prims.Y)) >>= fun xs =>
      (chooseBody (Tables.updateList (fun _ => default) (forsSkIdx vp) xs)).run [] >>= fun x =>
        (pure (Tables.updateList (fun _ => default) (forsSkIdx vp) xs, x.2, x.1) :
          OracleComp (WSpec prims) (Lazy.bWotsS A).State)
  wots_samples : (forsSkIdx vp).length = c.forsLeaves
  ud_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    (liftM ((rUd pkSeedDist (Lazy.bWotsS A)).distinguish ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2)
  ud_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPhase2O (gspec := gspec) A tbl hist root pk
      fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash) c.udP2
  pre_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    (liftM ((rPre pkSeedDist (Lazy.bWotsS A)).invert ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2)
  pre_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPhase2O (gspec := gspec) A tbl hist root pk
      fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash) c.preP2
  wtcr_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    (liftM ((rTcr pkSeedDist (Lazy.bWotsS A)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2)
  wtcr_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPhase2O (gspec := gspec) A tbl hist root pk
      fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash) c.wtcrP2

/-- **The direct resource theorem.** -/
theorem final_resources_direct (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesDirect A qs (directCounts vp qs) where
  prf := bPrfC_queryBound_exact A qs hA
  prfSuf := bPrfWC_queryBound_exact sufCheck A qs hA
  msg := Lazy.bPrfMsgL_queryBound A qs hA
  msg_draws := Lazy.bPrfMsgL_draws A qs hA
  msg_hashes := Lazy.bPrfMsgL_hashes A qs hA
  msgSuf := Lazy.bPrfMsgWL_queryBound sufCheck A qs hA
  msgSuf_draws := Lazy.bPrfMsgWL_draws sufCheck A qs hA
  msgSuf_hashes := Lazy.bPrfMsgWL_hashes sufCheck A qs hA
  itsr := Lazy.bItsrL_queryBound A qs hA
  itsr_draws := Lazy.bItsrL_draws A qs hA
  itsr_hashes := Lazy.bItsrL_hashes A qs hA
  fors_tcr_run := fun pk => forsTcr_choose_run hS A pk
  fors_dspr_run := fun pk => forsDspr_choose_run hS A pk
  fors_tcr_targets := fun pk => forsTcr_targets hS A pk
  fors_dspr_targets := fun pk => forsDspr_targets hS A pk
  fors_samples := ⟨Lazy.wotsSkIdx_length, (Lazy.bOpenPreS_targets hS).2⟩
  fors_tcr_phase2 := fun tbl tg ys pk => toTcr_bOpenPreS_forge_full A tbl tg ys pk
  fors_dspr_phase2 := fun tbl tg ys pk => toDspr_bOpenPreS_guess_full A tbl tg ys pk
  fors_phase2_hashes := fun pk ys => findOpenFull_hashes A qs hA pk ys
  fors_phase2_openings := fun pk ys => findOpenFull_openings A qs hA pk ys
  tcr_run := fun n pk => bTcrArS_choose_run_samples hS n A pk
  tcr_phase1 := fun n => bTcrArS_phase1 hS n A
  tcr_arity := ⟨rfl, rfl, rfl, rfl⟩
  tcr_samples := by
    show (Lazy.structSecIdx vp).length = openPreTargets vp + (wotsInsts vp).length * vp.params.len
    rw [Lazy.structSecIdx_length, ← Resources.openPreTargets_eq_length]
  tcr_phase2 := fun gspec n tbl L pk => bTcrArS_forge_open n A tbl L pk
  tcr_phase2_hashes := fun gspec tbl pk => tcrForgeOpen_hashes A qs hA tbl pk
  tcr_phase2_exact := fun tbl pk =>
    ⟨(tcr_structure_exact hS tbl pk).1, (tcr_structure_exact hS tbl pk).2.1⟩
  ud_phase1 := rUd_bWotsS_challenges hS A
  pre_phase1 := rPre_bWotsS_challenges hS A
  wtcr_phase1 := rTcr_bWotsS_targets hS A
  wots_choose := Lazy.bWotsS_choose_eq A
  wots_samples := by
    show (forsSkIdx vp).length = openPreTargets vp
    rw [Lazy.bWotsS_sampleCount, ← Resources.openPreTargets_eq_length]
  ud_phase2 := fun gspec tbl hist hist2 root pk =>
    wots_rUd_bWotsS_phase2_eq A tbl hist hist2 root pk
  ud_phase2_hashes := fun gspec tbl hist hist2 root pk =>
    wots_rUd_phase2_hashes A qs hA tbl hist hist2 root pk
  pre_phase2 := fun gspec tbl hist hist2 root pk =>
    wots_rPre_bWotsS_phase2_eq A tbl hist hist2 root pk
  pre_phase2_hashes := fun gspec tbl hist hist2 root pk =>
    wots_rPre_phase2_hashes A qs hA tbl hist hist2 root pk
  wtcr_phase2 := fun gspec tbl hist hist2 root pk =>
    wots_rTcr_bWotsS_phase2_eq A tbl hist hist2 root pk
  wtcr_phase2_hashes := fun gspec tbl hist hist2 root pk =>
    wots_rTcr_phase2_hashes A qs hA tbl hist hist2 root pk

/-- Resources of the adversaries built from an external (pure-interface) forger: `toInternal A`
makes at most `qs` signing queries, and the direct counts hold for it. -/
theorem final_resources_direct_external (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) (qs : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal A).main pk) (fun i => i.isRight = true) qs) ∧
      FinalResourcesDirect (toInternal A) qs (directCounts vp qs) :=
  ⟨toInternal_queryBound A qs hq, final_resources_direct hS _ qs (toInternal_queryBound A qs hq)⟩

end Resources2
end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction
namespace Resources2

theorem directCounts_128s (qs : ℕ) : directCounts Link.vp qs = directCounts128s qs := by
  have h1 : (wotsInsts Link.vp).length * Link.vp.params.len = 323449759100660631040 := by
    rw [← Resources.wotsChainTargets_eq, Resources.wotsChainTargets_128s_val]
  have h2 : Link.vp.params.k = 14 := rfl
  obtain ⟨a1, a2, a3, a4, -⟩ := arityTargets_128s
  unfold directCounts directCounts128s
  rw [a1, a2, a3, a4, Resources.wotsExecutedSteps_128s, h1, Resources.keygenReads_128s,
    Resources.signReads_128s, keygenHashes_128s, signHashes_128s,
    Resources.openPreTargets_128s_val, Resources.tcrTargets_128s_val, h2, forsSignHashes_128s,
    wotsSignHistHashes_128s, wotsWinHashes_128s, wotsPreHashes_128s, wotsTcrHashes_128s]

/-- **Direct resources at SLH-DSA-SHA2-128s, as numerals** (`directCounts128s qs`):
PRF `≤ 17920 + qs·182784` queries; lazy adversaries `≤ qs` game queries, `≤ 17920 + qs·182784`
draws, `≤ 269824 + qs·2007385` hash evaluations; FORS-leaf games: exactly
`528905046081400263933952` targets, `323449759100660631040 + 528905046081400263933952` samples,
phase 2 `≤ 269839 + qs·1950028` hash evaluations and `≤ 14·qs` simulated openings; class games:
`533756792467910173399552 / 528785142244921151848447 / 9241421688590303744 / 9223372036854775808`
targets (`F / H / T_len / T_k`), `1062560399506556770327551` targets + collection queries,
`529228495840500924564992` samples, phase 2 `≤ 269824 + qs·2007385 + 1062560399506556770327551`
hash evaluations; chains: `≤ 323449759100660631040` (UD, PRE) and `≤ 4851746386509909465600`
(TCR) challenges, phase 2 `≤ qs·121857 + 525 / 560 / 16800` hash evaluations. -/
theorem final_resources_direct_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesDirect A qs (directCounts128s qs) :=
  directCounts_128s qs ▸ final_resources_direct structural_128s A qs hA

#print axioms final_resources_direct
#print axioms final_resources_direct_external
#print axioms directCounts_128s
#print axioms final_resources_direct_128s

end Resources2
end Reduction
