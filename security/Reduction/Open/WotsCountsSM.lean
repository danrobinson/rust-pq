import Reduction.Open.WotsCounts

/-!
# Collection-oracle queries of phase 1 of `rUd`, `rPre`, `rTcr`, `rTcrT` at `bWotsS A`

Statements in the style of `Resources2.UdChallengesLe`: predicates generic in the WOTS-game
adversary `W` (`UdCollectionLe`, `PreCollectionLe`, `WTcrCollectionLe`, `WTcrTCollectionLe`):
in every run of phase 1 inside the SM game (every seed, both worlds for SM-UD), the game's own
record of collection queries (`z.2.2`, one entry per answered collection query) has length `≤ n`.

* `rUd_collection_le`, `rPre_collection_le` : `≤ wotsQc vp + #inst · (len · (w - 1))`;
* `rTcr_collection_le`, `rTcrT_collection_le` : `≤ wotsQc vp + #inst · len`;
* `bWotsS_collection_le` : `qc ≤ wotsQc vp` for `bWotsS A` in the WOTS game with a query counter
  (`wotsOraclesC`, `wotsOraclesC_proj`);
* `*_128s` : numerals.

No structural hypothesis is needed.  Proof: `simChoose_bWotsWith_count` (potential argument over
the memoised recursion of `chooseBody`), the per-query growth of the record (`ud_hO`, `pre_hO`,
`tcr_hO`) and syntactic budgets of the simulated signing program (`signProg_qb`: per chain with
digit `b`, `udStart` ≤ `b`, `preStart` 0, `tcrStart` ≤ 1 collection queries; the remaining
`w - 1 - b` chain steps are collection queries for `rUd`/`rPre` and targets for `rTcr`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal
open TweakableHash

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  (pkSeedDist : ProbComp prims.PkSeed)

open WotsFinal WotsUD

/-! ## The game oracles: growth of the collection record -/

theorem outer_unif_state {ι : Type} {spec : OracleSpec ι} {Sg : Type}
    (O₂ : QueryImpl spec (StateT Sg ProbComp)) (k : ℕ) (σ : Sg) :
    ∀ z ∈ support ((outer O₂ (Sum.inl k)).run σ), z.2 = σ := by
  intro z hz
  simp [outer] at hz
  obtain ⟨y, rfl⟩ := hz
  rfl

theorem ud_hO (world : SM_DT_UD_World) (pk : prims.PkSeed)
    (t : (unifSpec + (SM_DT_UD_challengeSpec prims.AdrsKey prims.Y +
      collectionSpec (wotsUdProblem vp prims pkSeedDist).thColl)).Domain)
    (σ : SM_DT_UD_State prims.AdrsKey) :
    ∀ z ∈ support ((outer (udO₂ pkSeedDist world pk) t).run σ),
      z.2.2.length ≤ σ.2.length + (if isColl t then 1 else 0) := by
  intro z hz
  rcases t with k | c | q
  · rw [outer_unif_state _ k σ z hz]; simp
  · by_cases h : (wotsUdProblem vp prims pkSeedDist).numTargets ≤ σ.1.length ∨
        ¬ TweakFresh id σ.1 σ.2 c
    · simp [outer, udO₂, SM_DT_UD_challengeOracle, h] at hz
      subst hz; simp
    · simp [outer, udO₂, SM_DT_UD_challengeOracle, h] at hz
      obtain ⟨x, -, rfl⟩ := hz
      simp
  · by_cases h : TweakReserved id σ.1 q.snd.1
    · simp [outer, udO₂, collectionOracle, h] at hz
      subst hz; simp
    · simp [outer, udO₂, collectionOracle, h] at hz
      subst hz; simp [isColl]

/-! ## SM-UD -/

theorem udColl_qb (key : prims.AdrsKey) (xs : List prims.Y) :
    IsQueryBoundP (udColl (vp := vp) pkSeedDist key xs) isColl 1 := by
  unfold udColl
  exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp) fun _ => isQueryBoundP_pure _ _ _

theorem udChal_qb (key : prims.AdrsKey) :
    IsQueryBoundP (udChal (vp := vp) pkSeedDist key) isColl 0 := by
  unfold udChal
  exact Lazy.qb_bind _ (n := 0) (m := 0) (by simp [isColl]) fun _ => isQueryBoundP_pure _ _ _

theorem udChain_qb (ca : Adrs) (x : prims.Y) (i s : ℕ) :
    IsQueryBoundP (chainWith (udChainHash (vp := vp) pkSeedDist) ca x i s) isColl s := by
  have h := Lazy.qb_chain isColl prims.core 1 (hash := udChainHash (vp := vp) pkSeedDist)
    (fun a y => udColl_qb pkSeedDist _ _) ca x i s
  rwa [Nat.mul_one] at h

/-- `udStart` on a chain with digit `b` makes at most `b` collection queries. -/
theorem udStart_qb (k : ℕ) (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (udStart (vp := vp) pkSeedDist k ca b) isColl b := by
  unfold udStart
  split_ifs with h
  · exact (Lazy.qb_bind _ (udChal_qb pkSeedDist _) fun y => udChain_qb pkSeedDist ca y _ _).mono
      (by omega)
  · exact (Lazy.qb_bind _ (qb_lift_isColl _ isColl (by rintro (_ | _ | _) h <;> simp_all [isColl]))
      fun y => udChain_qb pkSeedDist ca y _ _).mono (by omega)

theorem ud_pick_run (world : SM_DT_UD_World) (W : WotsGame.Adversary prims) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
        (rUd pkSeedDist W).pick).run ([], []) =
      (($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp _) >>= fun kf =>
        (simulateQ (outer (udO₂ pkSeedDist world pk))
          (WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
            (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], [])) := by
  show (simulateQ (outer (udO₂ pkSeedDist world pk))
    ((monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
      OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist) _) >>= fun kf =>
        WotsGame.simChoose W (wotsInsts vp) (udStart pkSeedDist kf.val)
          (udChainHash pkSeedDist) (udColl pkSeedDist))).run ([], []) = _
  rw [simulateQ_bind, StateT.run_bind, outer_lift, bind_map_left]

/-- In every run of phase 1 of `rUd pkSeedDist W` in the SM-UD game (both worlds, every seed),
the game has recorded at most `n` collection queries.  (A predicate generic in `W`, as
`Resources2.UdChallengesLe`.) -/
def UdCollectionLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) (n : ℕ) :
    Prop :=
  ∀ (world : SM_DT_UD_World) (pk : prims.PkSeed),
    ∀ z ∈ support ((simulateQ (SM_DT_UD_oracles world (wotsUdProblem vp prims pkSeedDist) pk)
      (rUd pkSeedDist W).pick).run ([], [])), z.2.2.length ≤ n

theorem rUd_bWotsWith_collection_le (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    UdCollectionLe pkSeedDist (Lazy.bWotsWith my A)
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  intro world pk z hz
  rw [ud_pick_run] at hz
  obtain ⟨kf, -, hz⟩ := (mem_support_bind_iff ..).mp hz
  have h := simChoose_bWotsWith_count (udO₂ pkSeedDist world pk) (fun σ => σ.2.length) isColl
    (ud_hO pkSeedDist world pk) (udStart pkSeedDist kf.val) (udChainHash pkSeedDist)
    (udColl pkSeedDist) 1 (vp.params.len * (vp.params.w - 1)) (udColl_qb pkSeedDist)
    (signProg_qb isColl _ _ (fun b => b) 1 (vp.params.w - 1)
      (fun ca b => udStart_qb pkSeedDist kf.val ca b) (fun a y => udColl_qb pkSeedDist _ _)
      (fun b hb => by omega)) my A ([], []) z hz
  simpa using h

/-- **Collection queries of `rUd pkSeedDist (bWotsS A)`**: at most
`qc + #inst · len · (w - 1)` in every run (both worlds, every seed). -/
theorem rUd_collection_le (A : Forger vp prims optRand pkSeedDist) :
    UdCollectionLe pkSeedDist (Lazy.bWotsS A)
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) :=
  rUd_bWotsWith_collection_le pkSeedDist _ A

/-! ## SM-PRE -/

theorem pre_hO (pk : prims.PkSeed)
    (t : (unifSpec + (SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y +
      collectionSpec (wotsPreProblem vp prims pkSeedDist).thColl)).Domain)
    (σ : SM_DT_PRE_State prims.AdrsKey prims.Y) :
    ∀ z ∈ support ((outer (preO₂ pkSeedDist pk) t).run σ),
      z.2.2.length ≤ σ.2.length + (if isColl t then 1 else 0) := by
  intro z hz
  rcases t with k | c | q
  · rw [outer_unif_state _ k σ z hz]; simp
  · by_cases h : (wotsPreProblem vp prims pkSeedDist).numTargets ≤ σ.1.length ∨
        ¬ TweakFresh Prod.fst σ.1 σ.2 c
    · simp [outer, preO₂, SM_DT_PRE_challengeOracle, h] at hz
      subst hz; simp
    · simp [outer, preO₂, SM_DT_PRE_challengeOracle, h] at hz
      obtain ⟨x, rfl⟩ := hz
      simp
  · by_cases h : TweakReserved Prod.fst σ.1 q.snd.1
    · simp [outer, preO₂, collectionOracle, h] at hz
      subst hz; simp
    · simp [outer, preO₂, collectionOracle, h] at hz
      subst hz; simp [isColl]

theorem preColl_qb (key : prims.AdrsKey) (xs : List prims.Y) :
    IsQueryBoundP (preColl (vp := vp) pkSeedDist key xs) isColl 1 := by
  unfold preColl
  exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp) fun _ => isQueryBoundP_pure _ _ _

theorem preChal_qb (key : prims.AdrsKey) :
    IsQueryBoundP (preChal (vp := vp) pkSeedDist key) isColl 0 := by
  unfold preChal
  exact Lazy.qb_bind _ (n := 0) (m := 0) (by simp [isColl]) fun _ => isQueryBoundP_pure _ _ _

/-- `preStart` makes no collection query. -/
theorem preStart_qb (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (preStart (vp := vp) pkSeedDist ca b) isColl 0 := by
  unfold preStart
  split_ifs with h
  · exact qb_lift_isColl _ isColl (by rintro (_ | _ | _) h <;> simp_all [isColl])
  · exact preChal_qb pkSeedDist _

/-- In every run of phase 1 of `rPre pkSeedDist W` in the SM-PRE game, the game has recorded at
most `n` collection queries. -/
def PreCollectionLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) (n : ℕ) :
    Prop :=
  ∀ pk : prims.PkSeed,
    ∀ z ∈ support ((simulateQ (SM_DT_PRE_oracles (wotsPreProblem vp prims pkSeedDist) pk)
      (rPre pkSeedDist W).choose).run ([], [])), z.2.2.length ≤ n

theorem rPre_bWotsWith_collection_le (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    PreCollectionLe pkSeedDist (Lazy.bWotsWith my A)
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  intro pk z hz
  have h := simChoose_bWotsWith_count (preO₂ pkSeedDist pk) (fun σ => σ.2.length) isColl
    (pre_hO pkSeedDist pk) (preStart pkSeedDist) (preChainHash pkSeedDist)
    (preColl pkSeedDist) 1 (vp.params.len * (vp.params.w - 1)) (preColl_qb pkSeedDist)
    (signProg_qb isColl _ _ (fun _ => 0) 1 (vp.params.w - 1)
      (fun ca b => preStart_qb pkSeedDist ca b) (fun a y => preColl_qb pkSeedDist _ _)
      (fun b hb => by omega)) my A ([], []) z hz
  simpa using h

/-- **Collection queries of `rPre pkSeedDist (bWotsS A)`**: at most
`qc + #inst · len · (w - 1)` in every run. -/
theorem rPre_collection_le (A : Forger vp prims optRand pkSeedDist) :
    PreCollectionLe pkSeedDist (Lazy.bWotsS A)
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) :=
  rPre_bWotsWith_collection_le pkSeedDist _ A

/-! ## SM-TCR on chains (`rTcr`, and `rTcrT` in the tight-cap game) -/

theorem tcr_hO (prob : SM_DT_TCR_Problem Unit prims.PkSeed prims.AdrsKey prims.Y prims.Y)
    (pk : prims.PkSeed)
    (t : (unifSpec + (SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
      collectionSpec prob.thColl)).Domain)
    (σ : SM_DT_TCR_State prims.AdrsKey prims.Y) :
    ∀ z ∈ support ((outer (SM_DT_TCR_challengeOracle prob pk +
        collectionOracle (Q := prims.AdrsKey × prims.Y) Prod.fst prob.thColl pk) t).run σ),
      z.2.2.length ≤ σ.2.length + (if isColl t then 1 else 0) := by
  intro z hz
  rcases t with k | c | q
  · rw [outer_unif_state _ k σ z hz]; simp
  · by_cases h : prob.numTargets ≤ σ.1.length ∨ ¬ TweakFresh Prod.fst σ.1 σ.2 c.1
    · simp [outer, SM_DT_TCR_challengeOracle, h] at hz
      subst hz; simp
    · simp [outer, SM_DT_TCR_challengeOracle, h] at hz
      subst hz; simp
  · by_cases h : TweakReserved Prod.fst σ.1 q.snd.1
    · simp [outer, collectionOracle, h] at hz
      subst hz; simp
    · simp [outer, collectionOracle, h] at hz
      subst hz; simp [isColl]

theorem wtcrColl_qb (key : prims.AdrsKey) (xs : List prims.Y) :
    IsQueryBoundP (wtcrColl (vp := vp) pkSeedDist key xs) isColl 1 := by
  unfold wtcrColl
  exact Lazy.qb_bind _ (n := 1) (m := 0) (by simp) fun _ => isQueryBoundP_pure _ _ _

theorem wtcrChal_qb (key : prims.AdrsKey) (x : prims.Y) :
    IsQueryBoundP (wtcrChal (vp := vp) pkSeedDist key x) isColl 0 := by
  unfold wtcrChal
  exact Lazy.qb_bind _ (n := 0) (m := 0) (by simp [isColl]) fun _ => isQueryBoundP_pure _ _ _

/-- `tcrStart` makes at most one collection query. -/
theorem tcrStart_qb (ca : Adrs) (b : ℕ) :
    IsQueryBoundP (tcrStart (vp := vp) pkSeedDist ca b) isColl 1 := by
  unfold tcrStart
  refine (Lazy.qb_bind _ (m := 1)
    (qb_lift_isColl _ isColl (by rintro (_ | _ | _) h <;> simp_all [isColl])) fun s => ?_).mono
    (by omega)
  split_ifs with h
  · exact isQueryBoundP_pure _ _ _
  · exact wtcrColl_qb pkSeedDist _ _

/-- In every run of phase 1 of `rTcr pkSeedDist W` in the SM-TCR game on chains, the game has
recorded at most `n` collection queries. -/
def WTcrCollectionLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) (n : ℕ) :
    Prop :=
  ∀ pk : prims.PkSeed,
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (rTcr pkSeedDist W).choose).run ([], [])), z.2.2.length ≤ n

/-- The same for `rTcrT pkSeedDist W` in the tight-cap game `wotsTcrProblemT`. -/
def WTcrTCollectionLe (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims)
    (n : ℕ) : Prop :=
  ∀ pk : prims.PkSeed,
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
      (rTcrT (vp := vp) pkSeedDist W).choose).run ([], [])), z.2.2.length ≤ n

theorem tcr_signProg_qb (a : Adrs) (m : prims.Y) :
    IsQueryBoundP (signProg (vp := vp) (tcrStart pkSeedDist) (tcrChainHash pkSeedDist) a m)
      isColl (vp.params.len * 1) :=
  signProg_qb isColl _ _ (fun _ => 1) 0 1
    (fun ca b => tcrStart_qb pkSeedDist ca b) (fun a y => wtcrChal_qb pkSeedDist _ _)
    (fun b hb => by omega) a m

theorem rTcr_bWotsWith_collection_le (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    WTcrCollectionLe pkSeedDist (Lazy.bWotsWith my A)
      (wotsQc vp + (wotsInsts vp).length * vp.params.len) := by
  intro pk z hz
  have h := simChoose_bWotsWith_count
    (SM_DT_TCR_challengeOracle (wotsTcrProblem vp prims pkSeedDist) pk +
      collectionOracle (Q := prims.AdrsKey × prims.Y) Prod.fst
        (wotsTcrProblem vp prims pkSeedDist).thColl pk)
    (fun σ => σ.2.length) isColl
    (tcr_hO (wotsTcrProblem vp prims pkSeedDist) pk) (tcrStart pkSeedDist)
    (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) 1 (vp.params.len * 1)
    (wtcrColl_qb pkSeedDist) (tcr_signProg_qb pkSeedDist) my A ([], []) z hz
  simpa using h

theorem rTcrT_bWotsWith_collection_le (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    WTcrTCollectionLe pkSeedDist (Lazy.bWotsWith my A)
      (wotsQc vp + (wotsInsts vp).length * vp.params.len) := by
  intro pk z hz
  have h := simChoose_bWotsWith_count
    (SM_DT_TCR_challengeOracle (wotsTcrProblemT vp prims pkSeedDist) pk +
      collectionOracle (Q := prims.AdrsKey × prims.Y) Prod.fst
        (wotsTcrProblemT vp prims pkSeedDist).thColl pk)
    (fun σ => σ.2.length) isColl
    (tcr_hO (wotsTcrProblemT vp prims pkSeedDist) pk) (tcrStart pkSeedDist)
    (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist) 1 (vp.params.len * 1)
    (wtcrColl_qb pkSeedDist) (tcr_signProg_qb pkSeedDist) my A ([], []) z hz
  simpa using h

/-- **Collection queries of `rTcr pkSeedDist (bWotsS A)`**: at most `qc + #inst · len`. -/
theorem rTcr_collection_le (A : Forger vp prims optRand pkSeedDist) :
    WTcrCollectionLe pkSeedDist (Lazy.bWotsS A)
      (wotsQc vp + (wotsInsts vp).length * vp.params.len) :=
  rTcr_bWotsWith_collection_le pkSeedDist _ A

/-- **Collection queries of `rTcrT pkSeedDist (bWotsS A)`** (tight-cap game): at most
`qc + #inst · len`. -/
theorem rTcrT_collection_le (A : Forger vp prims optRand pkSeedDist) :
    WTcrTCollectionLe pkSeedDist (Lazy.bWotsS A)
      (wotsQc vp + (wotsInsts vp).length * vp.params.len) :=
  rTcrT_bWotsWith_collection_le pkSeedDist _ A

/-! ## `qc`: collection queries of `bWotsS A` in the WOTS game itself

The WOTS game keeps no record of collection queries, so its phase-1 oracles are instrumented
with a counter (`wotsOraclesC`; forgetting the counter gives `WotsGame.oracles`,
`wotsOraclesC_proj`).  Every collection query is counted, refused or not. -/

/-- The signing oracle next to a counter (unchanged). -/
noncomputable def signC (k : ℕ) (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (WotsGame.signSpec prims) (StateT (List (WotsGame.Entry prims) × ℕ) ProbComp) :=
  fun q => StateT.mk fun s => (WotsGame.signOracle k insts pk q).run s.1 >>= fun r =>
    pure (r.1, (r.2, s.2))

/-- The collection oracle, counting every query. -/
def collC (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (WotsGame.collSpec prims) (StateT (List (WotsGame.Entry prims) × ℕ) ProbComp) :=
  fun q => StateT.mk fun s => (WotsGame.collOracle insts pk q).run s.1 >>= fun r =>
    pure (r.1, (r.2, s.2 + 1))

/-- `WotsGame.oracles k insts pk` with a counter of collection queries. -/
noncomputable def wotsOraclesC (k : ℕ) (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (WSpec prims) (StateT (List (WotsGame.Entry prims) × ℕ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (List (WotsGame.Entry prims) × ℕ) ProbComp) +
    (signC k insts pk + collC insts pk)

theorem wotsOraclesC_proj (k : ℕ) (insts : List Adrs) (pk : prims.PkSeed) {α : Type}
    (oa : OracleComp (WSpec prims) α) (s : List (WotsGame.Entry prims) × ℕ) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (wotsOraclesC k insts pk) oa).run s =
      (simulateQ (WotsGame.oracles k insts pk) oa).run s.1 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind, ih]
    rcases t with n | q | q
    · simp [wotsOraclesC, WotsGame.oracles]
    · simp [wotsOraclesC, WotsGame.oracles, signC, StateT.run_mk]
    · simp [wotsOraclesC, WotsGame.oracles, collC, StateT.run_mk]

/-- The counting semantics of the instrumented WOTS game. -/
noncomputable def wotsSem (k : ℕ) (pk : prims.PkSeed) :
    CSem vp prims (List (WotsGame.Entry prims) × ℕ) where
  sem oa s := (simulateQ (wotsOraclesC k (wotsInsts vp) pk) oa).run s
  hist s := s.1
  n s := s.2
  cC := 1
  K := 0
  sem_pure x s := by simp
  sem_bind oa f s := by simp [simulateQ_bind, StateT.run_bind]
  lift my s := by
    intro z hz
    have h1 : (monadLift my : OracleComp (WSpec prims) _) = my.liftComp (WSpec prims) := rfl
    rw [h1, wotsOraclesC, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget] at hz
    simp at hz
    obtain ⟨x, -, rfl⟩ := hz
    rfl
  coll q s := by
    intro z hz
    rw [simulateQ_spec_query] at hz
    simp [wotsOraclesC, collC, WotsGame.collOracle, StateT.run_mk] at hz
    subst hz
    exact ⟨rfl, le_rfl⟩
  sign q s := by
    intro z hz
    rw [simulateQ_spec_query] at hz
    by_cases h : q.1 ∉ wotsInsts vp ∨ q.1 ∈ s.1.map (·.1)
    · simp only [wotsOraclesC, signC, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        WotsGame.signOracle, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, if_pos h,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl ⟨rfl, rfl, le_rfl, h⟩
    · simp only [wotsOraclesC, signC, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        WotsGame.signOracle, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, if_neg h,
        StateT.run_monadLift, monadLift_self, bind_assoc, StateT.run_set, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨ss, -, rfl⟩ := hz
      rw [not_or, not_not] at h
      exact Or.inr ⟨_, _, rfl, rfl, h.1, h.2, le_rfl⟩

/-- In every run of phase 1 of `W` in the WOTS game with a query counter (any hybrid `k`, any
seed), at most `n` collection queries are made. -/
def WotsCollectionLe (W : WotsGame.Adversary prims) (n : ℕ) : Prop :=
  ∀ (k : ℕ) (pk : prims.PkSeed),
    ∀ z ∈ support ((simulateQ (wotsOraclesC k (wotsInsts vp) pk) W.choose).run ([], 0)),
      z.2.2 ≤ n

theorem bWotsWith_collection_le (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    WotsCollectionLe (Lazy.bWotsWith my A) (wotsQc vp) := by
  intro k pk z hz
  have h := (wotsSem (vp := vp) k pk).bWotsWith_choose_count my A ([], 0) rfl z hz
  simpa [wotsSem] using h

/-- **`qc`: collection queries of phase 1 of `bWotsS A` in the WOTS game**: at most
`wotsQc vp` in every run. -/
theorem bWotsS_collection_le (A : Forger vp prims optRand pkSeedDist) :
    WotsCollectionLe (Lazy.bWotsS A) (wotsQc vp) :=
  bWotsWith_collection_le pkSeedDist _ A

/-! ## SLH-DSA-SHA2-128s -/

theorem udCollB_128s :
    wotsQc Link.vp + (wotsInsts Link.vp).length * (Link.vp.params.len * (Link.vp.params.w - 1)) =
      1062560399506556770327551 := by
  have key : ∀ q N l w : ℕ, q = 1057708653120046860861951 → N = 9241421688590303744 → l = 35 →
      w = 16 → q + N * (l * (w - 1)) = 1062560399506556770327551 := by
    intro q N l w hq hN hl hw
    subst hq hN hl hw
    norm_num
  obtain ⟨-, -, -, -, -, -, hw, hlen, -⟩ := Resources.params_128s
  exact key _ _ _ _ wotsQc_128s Resources.wotsInsts_length_128s hlen hw

theorem tcrCollB_128s :
    wotsQc Link.vp + (wotsInsts Link.vp).length * Link.vp.params.len =
      1058032102879147521492991 := by
  have key : ∀ q N l : ℕ, q = 1057708653120046860861951 → N = 9241421688590303744 → l = 35 →
      q + N * l = 1058032102879147521492991 := by
    intro q N l hq hN hl
    subst hq hN hl
    norm_num
  obtain ⟨-, -, -, -, -, -, -, hlen, -⟩ := Resources.params_128s
  exact key _ _ _ wotsQc_128s Resources.wotsInsts_length_128s hlen

section S128

variable {optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y}
  (pkSeedDist : ProbComp Link.prims.PkSeed)

/-- `rUd pkSeedDist (bWotsS A)` at 128s: at most `1062560399506556770327551 ≈ 2^79.81`
collection queries. -/
theorem rUd_collection_le_128s (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    UdCollectionLe pkSeedDist (Lazy.bWotsS A) 1062560399506556770327551 :=
  udCollB_128s ▸ rUd_collection_le pkSeedDist A

theorem rPre_collection_le_128s (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    PreCollectionLe pkSeedDist (Lazy.bWotsS A) 1062560399506556770327551 :=
  udCollB_128s ▸ rPre_collection_le pkSeedDist A

/-- `rTcr pkSeedDist (bWotsS A)` at 128s: at most `1058032102879147521492991 ≈ 2^79.81`
collection queries. -/
theorem rTcr_collection_le_128s (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    WTcrCollectionLe pkSeedDist (Lazy.bWotsS A) 1058032102879147521492991 :=
  tcrCollB_128s ▸ rTcr_collection_le pkSeedDist A

theorem rTcrT_collection_le_128s (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    WTcrTCollectionLe pkSeedDist (Lazy.bWotsS A) 1058032102879147521492991 :=
  tcrCollB_128s ▸ rTcrT_collection_le pkSeedDist A

end S128

end Open
end Reduction

#print axioms Reduction.Open.rUd_collection_le
#print axioms Reduction.Open.rPre_collection_le
#print axioms Reduction.Open.rTcr_collection_le
#print axioms Reduction.Open.rTcrT_collection_le
#print axioms Reduction.Open.wotsOraclesC_proj
#print axioms Reduction.Open.bWotsS_collection_le
#print axioms Reduction.Open.rUd_collection_le_128s
#print axioms Reduction.Open.rPre_collection_le_128s
#print axioms Reduction.Open.rTcr_collection_le_128s
#print axioms Reduction.Open.rTcrT_collection_le_128s
