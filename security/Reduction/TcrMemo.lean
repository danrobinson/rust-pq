import Reduction.Resources2
import Reduction.TightCapsHeadline

/-!
# Arity-class SM-TCR adversaries that do not recompute the key structure (package W5)

`bTcrArS n A` / `bTcrArST n A` (the four arity-class SM-TCR adversaries of the headline) carry
the state `(tbl, L)` across the reveal of `PK.seed`: `tbl` is the sparse secret table and `L` is
the list of the `(tweak, input)` pairs of all hash calls of the key structure made in phase 1
(`TcrSplit.restrict` keeps it for its index translation; in the game `L = honestCalls tbl pk`,
`bTcrArS_choose_run`).  Their phase 2 nevertheless *recomputes* `honestCalls tbl pk` at the
revealed seed — `tcrTargets vp ≈ 2^79.81` evaluations of `Thash` at SHA2-128s
(`Resources2.tcr_structure_exact`).

`bTcrArM n A` (this file) is the same adversary with the recomputation removed:

* **phase 1** is literally the phase 1 of `bTcrArST n A` (`bTcrArM_choose`, `rfl`): same
  targets, same collection queries, same samples, same state `(tbl, L)`;
* **phase 2** uses the stored list `L` wherever the old adversary used the recomputed
  `honestCalls tbl pk`.  The collision search `findCollisionM` looks a verification call up in
  `L` *by its tweak* (first entry with that tweak — in the game the only one) and evaluates
  `Thash` only for that entry.

## Results

* `bTcrArM_experiment_eq`, `bTcrArM_advantage_eq`: the experiment of `bTcrArM n A` in the
  tight-cap class game **equals** that of `bTcrArST n A` (no inequality).
* Phase 1: `bTcrArM_choose_run`, `bTcrArM_choose_run_samples`, `bTcrArM_phase1`,
  `bTcrArM_targets_eq_cap` (transferred from W2/W3).
* Phase 2, own hash evaluations (`Reduction/Lazy` counting model: an open program in which
  every `Thash`/`H_msg` evaluation is a query of kind `.hash`):
  `memoForgeOpen A L pk` — key generation (one top tree), the forger's run with open signing,
  **verification of the forgery with the collision search interleaved** (all hash evaluations of
  the tail are queries here, unlike in W3 where the tail was only argued);
  `bTcrArM_forge_open` (interpretation = the adversary's phase-2 program, for every state);
  `memoForgeOpen_hashes`:
  `≤ keygenHashes + qs·signHashes + (1 + 2·verifyHashes)`,
  `verifyHashes = k·(1+a) + 1 + d·(len·(w-1) + 1 + h')`;
  at SHA2-128s `≤ 269824 + qs·2007385 + 7857` (`memoForgeOpen_hashes_128s`).
  No `tcrTargets`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

-- as in `Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-! ## Collision search by tweak lookup -/

/-- The collision test for one verification call `c` against the stored target list: look up the
first stored target with the tweak of `c`; if its input differs from that of `c` and the two
hash values coincide, report `(its index, input of c)`.  Two evaluations of `Thash` at most. -/
def chkM (pk : prims.PkSeed) (targets : List (prims.AdrsKey × List prims.Y))
    (c : prims.AdrsKey × List prims.Y) : Option (ℕ × List prims.Y) :=
  match targets[targets.findIdx fun t => decide (t.1 = c.1)]? with
  | none => none
  | some t =>
      if c.2 ≠ t.2 ∧ prims.Thash pk c.1 c.2 = prims.Thash pk t.1 t.2 then
        some (targets.findIdx (fun t => decide (t.1 = c.1)), c.2)
      else none

/-- The first call of `calls` that collides with the stored target of the same tweak. -/
def findCollisionM (pk : prims.PkSeed) (targets calls : List (prims.AdrsKey × List prims.Y)) :
    Option (ℕ × List prims.Y) :=
  calls.findSome? (chkM pk targets)

/-- Two search predicates on a list, `q` implying `p`, at most one position satisfying `p`:
the first `q`-position, if any, is the first `p`-position. -/
theorem findIdx_eq_of_unique {α : Type} (l : List α) (p q : α → Bool)
    (hqp : ∀ x, q x = true → p x = true)
    (huniq : ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      p l[i] = true → p l[j] = true → i = j)
    (hlt : l.findIdx q < l.length) :
    l.findIdx p < l.length ∧ l.findIdx p = l.findIdx q := by
  have hqj : q l[l.findIdx q] = true := List.findIdx_getElem (w := hlt)
  have hlt' : l.findIdx p < l.length :=
    List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem hlt, hqp _ hqj⟩
  exact ⟨hlt', huniq _ _ hlt' hlt (List.findIdx_getElem (w := hlt')) (hqp _ hqj)⟩

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.PkSeed] [Inhabited prims.Y] in
/-- On a target list with pairwise distinct tweaks the lookup test is the test of
`findCollision`. -/
theorem chkM_eq (pk : prims.PkSeed) (targets : List (prims.AdrsKey × List prims.Y))
    (hnd : (targets.map (·.1)).Nodup) (c : prims.AdrsKey × List prims.Y) :
    chkM pk targets c =
      (if targets.findIdx (fun t => decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧
            prims.Thash pk c.1 c.2 = prims.Thash pk t.1 t.2)) < targets.length then
          some (targets.findIdx (fun t => decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧
            prims.Thash pk c.1 c.2 = prims.Thash pk t.1 t.2)), c.2)
        else none) := by
  have huniq : ∀ (i j : ℕ) (hi : i < targets.length) (hj : j < targets.length),
      (fun t : prims.AdrsKey × List prims.Y => decide (t.1 = c.1)) targets[i] = true →
      (fun t : prims.AdrsKey × List prims.Y => decide (t.1 = c.1)) targets[j] = true → i = j := by
    intro i j hi hj h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    have hi' : i < (targets.map (·.1)).length := by simpa using hi
    have hj' : j < (targets.map (·.1)).length := by simpa using hj
    exact (hnd.getElem_inj_iff (hi := hi') (hj := hj')).1 (by simp [h1, h2])
  have hqp : ∀ x : prims.AdrsKey × List prims.Y,
      (fun t : prims.AdrsKey × List prims.Y => decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧
        prims.Thash pk c.1 c.2 = prims.Thash pk t.1 t.2)) x = true →
      (fun t : prims.AdrsKey × List prims.Y => decide (t.1 = c.1)) x = true := by
    intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact hx.1
  unfold chkM
  generalize hp : (fun t : prims.AdrsKey × List prims.Y => decide (t.1 = c.1)) = p at huniq hqp ⊢
  generalize hq : (fun t : prims.AdrsKey × List prims.Y => decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧
        prims.Thash pk c.1 c.2 = prims.Thash pk t.1 t.2)) = q at hqp ⊢
  by_cases hlt : targets.findIdx q < targets.length
  · obtain ⟨hlt', heq⟩ := findIdx_eq_of_unique targets p q hqp huniq hlt
    have hqj := (congrFun hq _).trans (List.findIdx_getElem (w := hlt))
    simp only [decide_eq_true_eq] at hqj
    rw [ite_eq_left hlt, heq, List.getElem?_eq_getElem hlt]
    simp only
    rw [ite_eq_left ⟨hqj.2.1, hqj.2.2⟩]
  · rw [ite_eq_right hlt]
    by_cases hlt' : targets.findIdx p < targets.length
    · rw [List.getElem?_eq_getElem hlt']
      simp only
      have hpj := (congrFun hp _).trans (List.findIdx_getElem (w := hlt'))
      simp only [decide_eq_true_eq] at hpj
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      refine hlt (List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem hlt',
        (congrFun hq _).symm.trans ?_⟩)
      simp only [decide_eq_true_eq]
      exact ⟨hpj, h1, h2⟩
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt')]

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.PkSeed] [Inhabited prims.Y] in
/-- **On a target list with pairwise distinct tweaks, `findCollisionM` is `findCollision`.** -/
theorem findCollisionM_eq (pk : prims.PkSeed) (targets calls : List (prims.AdrsKey × List prims.Y))
    (hnd : (targets.map (·.1)).Nodup) :
    findCollisionM pk targets calls = findCollision pk targets calls := by
  unfold findCollisionM findCollision
  exact congrArg (fun f => calls.findSome? f) (funext fun c => chkM_eq pk targets hnd c)

/-! ## The adversary -/

/-- The output translation of `TcrSplit.restrict` for the class "arity `n`": the answer `(j, m)`
against the all-arity target list `L` becomes an answer of the class game. -/
def classOut (prims : Primitives vp.params) [Inhabited prims.Y] (n : ℕ)
    (L : List (prims.AdrsKey × List prims.Y)) (jm : ℕ × List prims.Y) :
    ℕ × {xs : List prims.Y // xs.length = n} :=
  match L[jm.1]? with
  | some q => if h : q.2.length = n ∧ jm.2.length = n then
      (TcrSplit.classIdx (fun xs : List prims.Y => xs.length = n) L jm.1, ⟨jm.2, h.2⟩)
      else (L.length, arityDefault prims n)
  | none => (L.length, arityDefault prims n)

/-- Phase 2 of `bTcrArM n A`: recompute `PK.root` (one top tree), run the forger against the
table, verify the forgery and look every verification call up in the stored list `L`. -/
noncomputable def memoForge (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    ProbComp (ℕ × {xs : List prims.Y // xs.length = n}) := do
  let pk := idealPk vp prims s.1 pkSeed
  let z ← g2Run A s.1 pk
  return classOut prims n s.2
    ((findCollisionM pkSeed s.2 (verifyCalls pk z.1.1 z.1.2)).getD (0, []))

/-- **The arity-`n` SM-TCR adversary without structure recomputation**, against the tight-cap
class game.  Phase 1 is that of `bTcrArST n A`; the state is `(tbl, L)` with `L` the stored
`(tweak, input)` pairs of the phase-1 hash calls; phase 2 is `memoForge`. -/
noncomputable def bTcrArM (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n) where
  State := SecretTable vp prims × List (prims.AdrsKey × List prims.Y)
  choose := (simulateQ (TcrSplit.route (thashList vp prims pkSeedDist) (fun xs => xs.length = n)
    (tcrTargets vp)) (Lazy.bTcrS A).choose).run []
  forge := memoForge n A

/-- Phase 1 of `bTcrArM n A` is literally phase 1 of `bTcrArS n A` (which is that of
`bTcrArST n A`, `bTcrArST_choose`). -/
theorem bTcrArM_choose (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArM n A).choose = (bTcrArS n A).choose := rfl

theorem bTcrArM_forge (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArM n A).forge = memoForge n A := rfl

/-- Phase 2 of the old adversary, written out. -/
theorem bTcrArST_forge_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    (bTcrArST n A).forge (tbl, L) pkSeed =
      g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
        pure (classOut prims n L
          ((findCollision pkSeed (honestCalls tbl pkSeed)
            (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).getD (0, []))) := by
  have h1 : (bTcrArST n A).forge (tbl, L) pkSeed = (bTcrArS n A).forge (tbl, L) pkSeed :=
    congrFun (congrFun (bTcrArST_forge n A) (tbl, L)) pkSeed
  have h2 : (bTcrArS n A).forge (tbl, L) pkSeed = _ :=
    Resources2.tcr_restrict_forge_eq (fun xs : List prims.Y => xs.length = n)
      (arityDefault prims n) (Lazy.bTcrS A) (tbl, L) pkSeed
  have h3 : (Lazy.bTcrS A).forge tbl pkSeed =
      g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
        pure ((findCollision pkSeed (honestCalls tbl pkSeed)
          (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).getD (0, [])) := rfl
  rw [h1, h2]
  dsimp only
  rw [h3, bind_assoc]
  refine bind_congr fun z => ?_
  rw [pure_bind]
  unfold classOut
  generalize (findCollision pkSeed (honestCalls tbl pkSeed)
    (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).getD (0, []) = jm
  rcases L[jm.1]? with _ | q
  · rfl
  · rfl

/-- **Phase 2 agrees with the old adversary on every state the game can produce**: with
`L = honestCalls tbl pk` the lookup in the stored list gives what the recomputation gives. -/
theorem bTcrArM_forge_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (hL : L = honestCalls tbl pkSeed) :
    (bTcrArM n A).forge (tbl, L) pkSeed = (bTcrArST n A).forge (tbl, L) pkSeed := by
  rw [bTcrArST_forge_eq]
  show memoForge n A (tbl, L) pkSeed = _
  unfold memoForge
  refine bind_congr fun z => ?_
  dsimp only
  rw [findCollisionM_eq pkSeed _ _ (hL ▸ (honestCalls_nodup_length hS tbl pkSeed).1), hL]

/-- **Phase 1 of `bTcrArM n A` in the tight-cap class game**: one sparse table; the state handed
to phase 2 is `(tbl, honestCalls tbl pk)`; the game has recorded the arity-`n` calls as targets
and the tweaks of the others as collection queries. -/
theorem bTcrArM_choose_run (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArM n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          Lazy.sparseTable vp prims :=
  (TightCaps.run_recap_eq (thashArityProblem vp prims pkSeedDist n) (arityTargets vp n)
    (arityTargets_le_tcrTargets vp n) pk (bTcrArS n A).choose ([], [])
    (bTcrArS_within hS n A pk)).trans (bTcrArS_choose_run hS n A pk)

theorem bTcrArST_choose_run (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArST n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          Lazy.sparseTable vp prims :=
  (bTcrArST_run_eq hS n A pk).trans (bTcrArS_choose_run hS n A pk)

/-- **The experiments are equal.** -/
theorem bTcrArM_experiment_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Experiment (bTcrArM n A) = SM_DT_TCR_Experiment (bTcrArST n A) := by
  unfold SM_DT_TCR_Experiment
  refine bind_congr fun pk => ?_
  refine (congrArg (· >>= _) (bTcrArM_choose_run hS n A pk)).trans ?_
  refine Eq.trans ?_ (congrArg (· >>= _) (bTcrArST_choose_run hS n A pk)).symm
  refine (bind_map_left _ _ _).trans (Eq.trans ?_ (bind_map_left _ _ _).symm)
  refine bind_congr fun tbl => ?_
  exact congrArg (· >>= _) (bTcrArM_forge_eq hS n A tbl pk _ rfl)

/-- **Equal advantages**: `Adv(bTcrArM n A) = Adv(bTcrArST n A)` in the tight-cap class game. -/
theorem bTcrArM_advantage_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrArM n A) = SM_DT_TCR_Advantage (bTcrArST n A) := by
  unfold SM_DT_TCR_Advantage
  rw [bTcrArM_experiment_eq hS n A]

/-- `Adv(bTcrArM n A) = Adv(bTcrArS n A)` (the latter in the loose-cap game). -/
theorem bTcrArM_advantage_eq_loose (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrArM n A) = SM_DT_TCR_Advantage (bTcrArS n A) :=
  (bTcrArM_advantage_eq hS n A).trans (bTcrArST_advantage_eq hS n A)

/-! ## Phase 1: resources (transferred from W2/W3) -/

/-- **Phase 1 of `bTcrArM n A`, closed form**: `(structSecIdx vp).length` uniform values, then a
deterministic walk whose recorded game state is `gState` of the honest calls. -/
theorem bTcrArM_choose_run_samples (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArM n A).choose).run ([], []) =
      (fun tbl => ((tbl, honestCalls tbl pk),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          ((fun xs => Tables.updateList (fun _ => default) (Lazy.structSecIdx vp) xs) <$>
            Tables.sampleList prims.Y (Lazy.structSecIdx vp).length) := by
  rw [bTcrArM_choose_run hS, Lazy.sparseTable_eq]

/-- **Targets and collection queries of `bTcrArM n A`** in the tight-cap class game: in every
run exactly `arityTargets vp n` targets, and targets plus collection queries are the
`tcrTargets vp` hash calls of the key structure (`Resources2.TcrPhase1Counts`). -/
theorem bTcrArM_phase1 (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    Resources2.TcrPhase1Counts (bTcrArM n A) (arityTargets vp n) (tcrTargets vp) :=
  Resources2.tcrPhase1Counts_of_run _ _ _ (Lazy.sparseTable vp prims)
    (fun pk tbl => ((tbl, honestCalls tbl pk),
      TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)))
    (fun pk => bTcrArM_choose_run hS n A pk)
    (fun pk tbl => ⟨(bTcrArS_targets hS n tbl pk).1, (bTcrArS_targets hS n tbl pk).2.1⟩)

set_option linter.constructorNameAsVariable false in
/-- The cap of the tight class game is attained by `bTcrArM n A` in every run. -/
theorem bTcrArM_targets_eq_cap (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArM n A).choose).run ([], [])),
      z.2.1.length = (thashArityProblemT vp prims pkSeedDist n).numTargets := by
  intro z hz
  rw [bTcrArM_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact (bTcrArS_targets hS n tbl pk).1

set_option linter.constructorNameAsVariable false in
/-- The state handed to phase 2 is `(tbl, honestCalls tbl pk)`: the stored list has
`tcrTargets vp` entries with pairwise distinct tweaks (the reduction's memory). -/
theorem bTcrArM_state (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArM n A).choose).run ([], [])),
      ∃ tbl : SecretTable vp prims, z.1 = (tbl, honestCalls tbl pk) ∧
        (honestCalls tbl pk).length = tcrTargets vp ∧ ((honestCalls tbl pk).map (·.1)).Nodup := by
  intro z hz
  rw [bTcrArM_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact ⟨tbl, rfl, (honestCalls_nodup_length hS tbl pk).2, (honestCalls_nodup_length hS tbl pk).1⟩

/-! ## Phase 2 as an open program: own hash evaluations -/

namespace Resources2

variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ Lazy.closedQ

/-- One hash-oracle query of the free verification program. -/
def thQ (prims : Primitives vp.params) (key : prims.AdrsKey) (xs : List prims.Y) :
    OracleComp (thSpec prims) prims.Y :=
  (liftM ((thSpec prims).query (key, xs)) : OracleComp (thSpec prims) prims.Y)

/-- Verification of a signature (FORS public key from the signature, then the hypertree root)
as a program over the hash oracle; `parts` is the split message digest. -/
noncomputable def verifyFree (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (sig : GeneralScheme.SignatureCore vp prims.core) : OracleComp (thSpec prims) prims.Y :=
  forsPkFromSigWith prims.core (fun a x => thQ prims (prims.adrsToKey a) [x])
      (fun a l r => thQ prims (prims.adrsToKey a) [l, r])
      (fun a xs => thQ prims (prims.adrsToKey a) xs)
      sig.fors parts.md.toList parts.forsAdrs >>= fun forsPk =>
    GeneralHypertree.pkFromSigWith vp prims.core (fun a x => thQ prims (prims.adrsToKey a) [x])
      (fun a xs => thQ prims (prims.adrsToKey a) xs)
      (fun a l r => thQ prims (prims.adrsToKey a) [l, r])
      forsPk sig.hypertree pkSeed parts

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem logImpl_thQ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    simulateQ' (logImpl pk) (thQ prims key xs) = logTh pk key xs := by
  simp only [thQ, simulateQ_spec_query]
  rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- **`verifyCalls` is the log of the free verification program** under `prims.Thash`: one entry
per evaluation. -/
theorem verifyCalls_eq_free (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    verifyCalls pk msg sig =
      ((simulateQ (logImpl pk.pkSeed)
        (verifyFree pk.pkSeed (digestParts pk sig.randomness msg) sig)).run []).2 := by
  have h : simulateQ' (logImpl pk.pkSeed)
      (verifyFree pk.pkSeed (digestParts pk sig.randomness msg) sig) =
      (forsPkFromSigWith prims.core
          (fun a x => logTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => logTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a xs => logTh pk.pkSeed (prims.adrsToKey a) xs)
          sig.fors (digestParts pk sig.randomness msg).md.toList
          (digestParts pk sig.randomness msg).forsAdrs >>= fun forsPk =>
        GeneralHypertree.pkFromSigWith vp prims.core
          (fun a x => logTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => logTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => logTh pk.pkSeed (prims.adrsToKey a) [l, r])
          forsPk sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg)) := by
    unfold verifyFree
    rw [MonadHom.mmap_bind, forsPkFromSigWith_natural (simulateQ' (logImpl pk.pkSeed)) prims.core
      _ _ _ _ _ _
      (fun a y => logImpl_thQ pk.pkSeed _ _) (fun a l r => logImpl_thQ pk.pkSeed _ _)
      (fun a ys => logImpl_thQ pk.pkSeed _ _)]
    exact bind_congr fun forsPk => sub_recoverFromPositionWith_natural prims.core
      (simulateQ' (logImpl pk.pkSeed)) _ _ _ _
      _ _ (fun a y => logImpl_thQ pk.pkSeed _ _) (fun a ys => logImpl_thQ pk.pkSeed _ _)
      (fun a l r => logImpl_thQ pk.pkSeed _ _) _ _ _ _ _ _
  rw [← simulateQ'_apply, h]
  rfl

/-- Hash evaluations of one verification (without `H_msg`):
`k·(1+a) + 1 + d·(len·(w-1) + 1 + h')`. -/
def verifyHashes (vp : ValidatedParams) : ℕ :=
  vp.params.k * (1 + vp.params.a) + 1 +
    vp.params.d * (vp.params.len * (vp.params.w - 1) + 1 + vp.params.hp)

theorem qb_recover {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
    (core : CorePrimitives vp.params)
    {hash : Adrs → core.Y → OracleComp spec core.Y}
    {compress : Adrs → List core.Y → OracleComp spec core.Y}
    {nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y} (cF cT cH : ℕ)
    (hhash : ∀ a y, IsQueryBoundP (hash a y) p cF)
    (hcompress : ∀ a ys, IsQueryBoundP (compress a ys) p cT)
    (hnode : ∀ a l r, IsQueryBoundP (nodeHash a l r) p cH) (pk : core.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) (sigs : Vector (XmssSig vp.params core) layers),
      IsQueryBoundP (GeneralHypertree.recoverFromPositionWith vp core hash compress nodeHash pk
        pos layers h msg sigs) p (layers * Lazy.xmssPkB vp cF cT cH)
  | 0, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      exact isQueryBoundP_pure _ _ _
  | 1, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith, Nat.one_mul]
      exact Lazy.qb_xmssPk p core cF cT cH hhash hcompress hnode _ _ _ _
  | layers + 2, pos, h, msg, sigs => by
      rw [GeneralHypertree.recoverFromPositionWith]
      refine (Lazy.qb_bind p (Lazy.qb_xmssPk p core cF cT cH hhash hcompress hnode _ _ _ _)
        fun root => qb_recover p core cF cT cH hhash hcompress hnode pk (layers + 1) _ _ _ _).mono
        ?_
      exact Nat.le_of_eq (by ring)

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- **The free verification program makes at most `verifyHashes vp` hash-oracle queries**,
whatever the answers. -/
theorem verifyFree_bound (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    IsQueryBoundP (verifyFree pkSeed parts sig) (fun _ => True) (verifyHashes vp) := by
  have hq : ∀ (key : prims.AdrsKey) (xs : List prims.Y),
      IsQueryBoundP (thQ prims key xs) (fun _ => True) 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  unfold verifyFree
  refine (Lazy.qb_bind _ (Lazy.qb_forsPk (fun _ => True) prims.core 1 1 1
    (fun a y => hq _ _) (fun a ys => hq _ _) (fun a l r => hq _ _) _ _ _) fun forsPk =>
    qb_recover (fun _ => True) prims.core 1 1 1 (fun a y => hq _ _) (fun a ys => hq _ _)
      (fun a l r => hq _ _) pkSeed vp.params.d _ _ _ _).mono ?_
  unfold verifyHashes Lazy.xmssPkB
  simp only [Nat.mul_one]
  exact Nat.le_refl _

/-- One `Thash` evaluation of an open program. -/
def hashQ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    OracleComp (Lazy.OSpec prims gspec) prims.Y :=
  (liftM ((Lazy.OSpec prims gspec).query
    (.inr (.inr (.inr (PublicHashQuery.thash pk key xs))))) :
    OracleComp (Lazy.OSpec prims gspec) prims.Y)

/-- **The hash callback of the memoised verification.**  For a verification call `t`: evaluate
`Thash` at `t` (one hash query; the value is returned to the verification), look the tweak of
`t` up in the stored list `L`; if an entry with a different input is found, evaluate `Thash` at
that entry (second hash query) and compare.  The state is the first collision found so far. -/
def collO (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y)) :
    QueryImpl (thSpec prims)
      (StateT (Option (ℕ × List prims.Y)) (OracleComp (Lazy.OSpec prims gspec))) :=
  fun t => StateT.mk fun r => do
    let y ← hashQ (gspec := gspec) pk t.1 t.2
    match L[L.findIdx fun q => decide (q.1 = t.1)]? with
    | none => pure (y, r)
    | some q =>
        if t.2 ≠ q.2 then do
          let y' ← hashQ (gspec := gspec) pk q.1 q.2
          pure (y, r.or (if y = y' then some (L.findIdx (fun q => decide (q.1 = t.1)), t.2)
            else none))
        else pure (y, r)

theorem hashQ_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed) (key : prims.AdrsKey)
    (xs : List prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (hashQ (gspec := gspec) pk key xs) = pure (prims.Thash pk key xs) := by
  simp [hashQ, Lazy.tblImpl, PublicHash.impl]

/-- One step of `collO` under the table interpretation: the hash value, and the collision state
updated by `chkM`. -/
theorem collO_step (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (L : List (prims.AdrsKey × List prims.Y)) (t : prims.AdrsKey × List prims.Y)
    (r : Option (ℕ × List prims.Y)) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        ((collO (gspec := gspec) pk L t).run r) =
      pure (prims.Thash pk t.1 t.2, r.or (chkM pk L t)) := by
  unfold collO chkM
  simp only [StateT.run_mk, simulateQ_bind, hashQ_tbl, pure_bind]
  generalize L[L.findIdx fun q => decide (q.1 = t.1)]? = o
  rcases o with _ | q
  · simp
  · by_cases hne : t.2 = q.2
    · simp [hne]
    · by_cases hy : prims.Thash pk t.1 t.2 = prims.Thash pk q.1 q.2 <;>
        simp [hne, hy, hashQ_tbl]

/-- **Interpretation of the memoised verification.**  Under the table interpretation, running a
hash-oracle program through `collO` returns the program's value and
`findCollisionM pk L (its call log)`. -/
theorem collO_tbl {α : Type} (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (L : List (prims.AdrsKey × List prims.Y)) (P : OracleComp (thSpec prims) α)
    (Lg : List (prims.AdrsKey × List prims.Y)) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        ((simulateQ (collO (gspec := gspec) pk L) P).run (findCollisionM pk L Lg)) =
      pure (((simulateQ (logImpl pk) P).run Lg).1,
        findCollisionM pk L ((simulateQ (logImpl pk) P).run Lg).2) := by
  induction P using OracleComp.inductionOn generalizing Lg with
  | pure a => simp; exact ⟨rfl, rfl⟩
  | query_bind t k ih =>
    have h1 : (simulateQ (logImpl pk) (liftM ((thSpec prims).query t) >>= k)).run Lg =
        (simulateQ (logImpl pk) (k (prims.Thash pk t.1 t.2))).run (Lg ++ [t]) := by
      rw [simulateQ_bind, simulateQ_spec_query]; rfl
    have h2 : findCollisionM pk L (Lg ++ [t]) = (findCollisionM pk L Lg).or (chkM pk L t) := by
      unfold findCollisionM
      rw [List.findSome?_append]
      simp
    rw [h1, ← ih _ (Lg ++ [t]), h2]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, collO_step, pure_bind]

/-- Each step of `collO` makes at most two hash queries. -/
theorem collO_step_bound (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (K : Lazy.Kind) (t : prims.AdrsKey × List prims.Y) (r : Option (ℕ × List prims.Y)) :
    IsQueryBoundP ((collO (gspec := gspec) pk L t).run r) (fun t => Lazy.kind t = K) 2 := by
  have hq : ∀ (key : prims.AdrsKey) (xs : List prims.Y),
      IsQueryBoundP (hashQ (gspec := gspec) pk key xs) (fun t => Lazy.kind t = K) 1 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  unfold collO
  simp only [StateT.run_mk]
  refine Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 1) (hq _ _) fun y => ?_
  generalize L[L.findIdx fun q => decide (q.1 = t.1)]? = o
  rcases o with _ | q
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · show IsQueryBoundP (if t.2 ≠ q.2 then _ else _) _ _
    by_cases hne : t.2 ≠ q.2
    · rw [ite_eq_left hne]
      exact Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0) (hq _ _)
        fun y' => isQueryBoundP_pure _ _ _
    · rw [ite_eq_right hne]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-- **Phase 2 of `bTcrArM n A` as an open program** (before the hash-free output translation
`classOut`): key generation, the forger's run with open signing, one `H_msg` evaluation for the
forgery, then verification of the forgery with the collision search against the stored list `L`
interleaved.  Every `Thash`/`H_msg` evaluation is a hash query; no part of the key structure is
recomputed. -/
noncomputable def memoForgeOpen (A : Forger vp prims optRand pkSeedDist)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) := do
  let root ← Lazy.openKeygen prims gspec pkSeed
  let z ← runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift
    (fun m R => Lazy.openSign prims gspec m pkSeed root R)
  let dg ← (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
    OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))
  let c ← (simulateQ (collO (gspec := gspec) pkSeed L)
    (verifyFree pkSeed (splitDigest vp.params dg) z.1.2)).run none
  return c.2.getD (0, [])

/-- **Interpretation.**  With the secret oracle read from the table and the hash oracle evaluated
by `prims`, `memoForgeOpen A L pkSeed` is phase 2 of `bTcrArM n A` at the state `(tbl, L)`
before the output translation — for every state. -/
theorem memoForgeOpen_tbl (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (memoForgeOpen A L pkSeed) =
      (liftM (g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
        pure ((findCollisionM pkSeed L
          (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).getD (0, []))) :
        OracleComp (unifSpec + gspec) _) := by
  have hrun : simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (runForgerLog A ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ lazyRandomizerLift
        (fun m R => Lazy.openSign prims gspec m pkSeed (idealRoot vp prims tbl pkSeed) R)) =
      (liftM (g2Run A tbl (idealPk vp prims tbl pkSeed)) : OracleComp (unifSpec + gspec) _) :=
    (wots_runForgerLog_tbl A tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ _ _ lazyRandomizerLift
      (fun m R => pure (idealSign vp prims tbl m ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ R))
      (fun log m a => Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl _)
      (fun m R => Lazy.openSign_tbl tbl m ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ R)).trans
    (wots_runForgerLog_pure_eq_liftM_g2RunWith A ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ _)
  have hmsg : ∀ (R : prims.Y) (root : prims.Y) (m : List Byte),
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (PublicHash.hmsg prims.core R pkSeed root m :
          OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m)) =
      pure (prims.Hmsg R pkSeed root m) := by
    intro R root m
    simp [PublicHash.hmsg, Lazy.tblImpl, PublicHash.impl]
  unfold memoForgeOpen
  simp only [simulateQ_bind, simulateQ_pure]
  rw [Lazy.openKeygen_tbl, pure_bind, hrun, liftM_bind]
  refine bind_congr fun z => ?_
  rw [hmsg, pure_bind]
  have hc := collO_tbl (gspec := gspec) tbl pkSeed L
    (verifyFree pkSeed (splitDigest vp.params
      (prims.Hmsg z.1.2.randomness pkSeed (idealRoot vp prims tbl pkSeed) z.1.1)) z.1.2) []
  have hnil : findCollisionM pkSeed L [] = none := rfl
  rw [hnil] at hc
  rw [hc, pure_bind, verifyCalls_eq_free]
  rfl

/-- **Phase 2 of `bTcrArM n A`** is the interpretation of `memoForgeOpen A L pk` followed by the
hash-free output translation `classOut` — for every state `(tbl, L)`. -/
theorem bTcrArM_forge_open (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    (liftM ((bTcrArM n A).forge (tbl, L) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (memoForgeOpen A L pk) >>= fun jm => pure (classOut prims n L jm) := by
  rw [memoForgeOpen_tbl]
  show (liftM (memoForge n A (tbl, L) pk) : OracleComp (unifSpec + gspec) _) = _
  unfold memoForge
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]

/-- Queries of kind `K` of the open phase-2 program. -/
theorem memoForgeOpen_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (memoForgeOpen (gspec := gspec) A L pkSeed) (fun t => Lazy.kind t = K)
      (Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        qs * Lazy.signB vp (Lazy.ind K .sec) (Lazy.ind K .hash) + (1 + verifyHashes vp * 2)) := by
  have hrun : ∀ root : prims.Y,
      IsQueryBoundP (runForgerLog (spec := gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))
        A ⟨pkSeed, root⟩ lazyRandomizerLift
        (fun m R => Lazy.openSign prims gspec m pkSeed root R)) (fun t => Lazy.kind t = K)
        (qs * Lazy.signB vp (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
    intro root
    unfold runForgerLog
    refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · cases t with
      | inl n => simp at ht
      | inr m =>
        have hstep := Lazy.qb_bind (fun t => Lazy.kind t = K)
          (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK (optRand ⟨pkSeed, root⟩)) fun addrnd =>
          Lazy.qb_bind (fun t => Lazy.kind t = K)
            (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
              (hspec := publicHashSpec prims.core) K hK (lazyRandomizer s m addrnd)) fun R =>
            Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
              (Lazy.openSign_kindBound (gspec := gspec) K m pkSeed root R)
              fun sig => isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
        simpa [logSignOracle, lazyRandomizerLift] using hstep
    · cases t with
      | inl n =>
        simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
        have h0 := Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
          (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK
            (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
        exact h0
      | inr m => simp at ht
  have hver : ∀ (parts : DigestParts vp.params) (sig : GeneralScheme.SignatureCore vp prims.core),
      IsQueryBoundP ((simulateQ (collO (gspec := gspec) pkSeed L)
        (verifyFree pkSeed parts sig)).run none) (fun t => Lazy.kind t = K)
        (verifyHashes vp * 2) := fun parts sig =>
    IsQueryBoundP.simulateQ_run_of_step_le (cost := 2) (q := fun t => Lazy.kind t = K)
      (verifyFree_bound pkSeed parts sig) (fun t ht s => collO_step_bound pkSeed L K t s)
      (fun t ht s => absurd trivial ht) none
  have hmsg : ∀ (R root : prims.Y) (m : List Byte),
      IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed root m :
        OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m)) (fun t => Lazy.kind t = K) 1 :=
    fun R root m => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  unfold memoForgeOpen
  exact (Lazy.qb_bind _ (Lazy.openKeygen_kindBound K pkSeed) fun root =>
    Lazy.qb_bind _ (hrun root) fun z =>
      Lazy.qb_bind _ (hmsg _ _ _) fun dg =>
        Lazy.qb_bind _ (m := 0) (hver _ _) fun c => isQueryBoundP_pure _ _ _).mono (by omega)

/-- **Own hash evaluations of phase 2 of `bTcrArM n A`** (everything: key generation, signing
simulation, `H_msg` of the forgery, verification of the forgery, collision search): at most
`keygenHashes + qs·signHashes + (1 + 2·verifyHashes)`.  No `tcrTargets`. -/
theorem memoForgeOpen_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (memoForgeOpen (gspec := gspec) A L pkSeed) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + verifyHashes vp * 2)) :=
  (memoForgeOpen_kindBound A .hash (by decide) qs hA L pkSeed).mono
    (Nat.add_le_add_right (Nat.add_le_add Lazy.keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using Lazy.signB_hash (vp := vp)))) _)

/-- Secret-table reads of phase 2 (none in the verification tail). -/
theorem memoForgeOpen_reads (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (memoForgeOpen (gspec := gspec) A L pkSeed) (fun t => Lazy.kind t = .sec)
      (Lazy.keygenB vp 1 0 + qs * Lazy.signB vp 1 0 + (1 + verifyHashes vp * 2)) := by
  simpa [Lazy.ind] using memoForgeOpen_kindBound (gspec := gspec) A .sec (by decide) qs hA L pkSeed

end Resources2

end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction
namespace Resources2

theorem verifyHashes_128s : verifyHashes Link.vp = 3928 := by decide

/-- Own hash evaluations of phase 2 of `bTcrArM n A` at SHA2-128s:
`≤ 269824 + qs·2007385 + 7857`. -/
theorem memoForgeOpen_hashes_128s {ι : Type} {gspec : OracleSpec ι}
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (L : List (Link.prims.AdrsKey × List Link.prims.Y)) (pkSeed : Link.prims.PkSeed) :
    IsQueryBoundP (memoForgeOpen (gspec := gspec) A L pkSeed) (fun t => Lazy.kind t = .hash)
      (269824 + qs * 2007385 + 7857) := by
  have h := memoForgeOpen_hashes (gspec := gspec) A qs hA L pkSeed
  rwa [keygenHashes_128s, signHashes_128s, verifyHashes_128s] at h

end Resources2

#print axioms findCollisionM_eq
#print axioms bTcrArM_experiment_eq
#print axioms bTcrArM_advantage_eq
#print axioms bTcrArM_advantage_eq_loose
#print axioms bTcrArM_choose_run
#print axioms bTcrArM_choose_run_samples
#print axioms bTcrArM_phase1
#print axioms bTcrArM_targets_eq_cap
#print axioms bTcrArM_state
#print axioms Resources2.verifyCalls_eq_free
#print axioms Resources2.verifyFree_bound
#print axioms Resources2.collO_tbl
#print axioms Resources2.memoForgeOpen_tbl
#print axioms Resources2.bTcrArM_forge_open
#print axioms Resources2.memoForgeOpen_hashes
#print axioms Resources2.memoForgeOpen_hashes_128s
#print axioms bTcrArM
#print axioms memoForge

end Reduction
