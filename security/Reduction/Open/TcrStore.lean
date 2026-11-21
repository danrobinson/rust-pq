/-
Work package OPEN, O9 (stretch): the ANSWER-STORING variant `bTcrArA n A` of the class SM-TCR
adversaries `bTcrArM n A` (`Reduction/TcrMemo.lean`).

`bTcrArM n A` keeps, across the reveal of `PK.seed`, the secret table `tbl` and the list `L` of
the `(tweak, input)` pairs of all hash calls of the key structure.  `bTcrArA n A` keeps in
addition the list `S` of the ANSWERS `((tweak, input), value)` its two oracles (challenge and
collection oracle) returned in phase 1; its second phase is the second phase of `bTcrArM n A`
run with the tweakable hash "look `(tweak, input)` up in `S`; on a miss, hash" (`lkT`).

This file: the recording wrapper `routeA` with its own coupling (`choose_couplingA`), the
adversary, its first phase in closed form (`bTcrArA_choose_run`), the unconditional agreement of
the second phases on sound stores (`storeForge_eq`), and the equality of experiments
(`bTcrArA_experiment_eq`).  Open program and counts: `Reduction/Open/TcrStoreCount.lean`.
-/
import Reduction.Open.WithHash
import Reduction.TcrMemoHeadline

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open TweakableHash TcrSplit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Generic: the wrapper of `TcrSplit.route` that also records the oracle answers -/

section Generic

variable {PkSeed Tweak Y : Type} [DecidableEq Tweak]

/-- Record the answer `some y` to a target query `c = (tweak, input)` of the wrapped adversary;
anything else (uniform bits, a refused query) leaves the store unchanged. -/
def recAns (th : TweakableHash PkSeed Tweak (List Y) Y) (N : ℕ) :
    (q : (spec₀ th N).Domain) → (spec₀ th N).Range q →
      List ((Tweak × List Y) × Y) → List ((Tweak × List Y) × Y)
  | .inl _, _, S => S
  | .inr (.inl c), some y, S => S ++ [(c, y)]
  | .inr (.inl _), none, S => S
  | .inr (.inr _), _, S => S

/-- One step of the recording wrapper: the step of `TcrSplit.route`, then the answer handed back
to the wrapped adversary is appended to the store. -/
def routeStepA (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) [DecidablePred P]
    (N : ℕ) (q : (spec₀ th N).Domain)
    (s : List (Tweak × List Y) × List ((Tweak × List Y) × Y)) :
    OracleComp (spec₁ th P N)
      ((spec₀ th N).Range q × (List (Tweak × List Y) × List ((Tweak × List Y) × Y))) :=
  (fun z => (z.1, (z.2, recAns th N q z.1 s.2))) <$> routeStep th P N q s.1

/-- The recording wrapper as a stateful handler; state `(L, S)`: accepted targets, and the
answers of the challenge / collection oracle to them. -/
def routeA (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) [DecidablePred P]
    (N : ℕ) : QueryImpl (spec₀ th N)
      (StateT (List (Tweak × List Y) × List ((Tweak × List Y) × Y))
        (OracleComp (spec₁ th P N))) :=
  fun q => StateT.mk (routeStepA th P N q)

/-- The targets `L` annotated with their hash values at the seed `pk`. -/
def ann (th : TweakableHash PkSeed Tweak (List Y) Y) (pk : PkSeed) (L : List (Tweak × List Y)) :
    List ((Tweak × List Y) × Y) :=
  L.map fun c => (c, th.eval pk c.1 c.2)

theorem ann_append (th : TweakableHash PkSeed Tweak (List Y) Y) (pk : PkSeed)
    (L : List (Tweak × List Y)) (c : Tweak × List Y) :
    ann th pk L ++ [(c, th.eval pk c.1 c.2)] = ann th pk (L ++ [c]) := by
  simp [ann]

variable (P : List Y → Prop) [DecidablePred P]
variable (th : TweakableHash PkSeed Tweak (List Y) Y) (N : ℕ) (pk : PkSeed)

/-- **Coupling for the recording wrapper** (the analogue of `TcrSplit.choose_coupling`): in the
class game at seed `pk`, started in the state corresponding to accepted targets `L` with the
store `ann th pk L`, the wrapped run is one run of the adversary in its own game, and the final
store is `ann th pk` of the final target list: every accepted target with its hash value at
`pk`. -/
theorem choose_couplingA {α : Type} (oa : OracleComp (spec₀ th N) α)
    (L : List (Tweak × List Y)) :
    (simulateQ (SM_DT_TCR_oracles (classProblem th P N) pk)
        ((simulateQ (routeA th P N) oa).run (L, ann th pk L))).run (gState P L) =
      (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk) oa).run (L, []) >>=
        fun z => pure ((z.1, (z.2.1, ann th pk z.2.1)), gState P z.2.1) := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases q with n | ⟨t, xs⟩ | q
    · rw [run_unif₀]
      have h1 : (routeA th P N (.inl n)).run (L, ann th pk L) =
          (fun u => (u, (L, ann th pk L))) <$> liftM ((spec₁ th P N).query (.inl n)) := by
        show (fun z => _) <$> ((fun u => (u, L)) <$> _) = _
        rw [Functor.map_map]
        rfl
      rw [h1]
      simp only [simulateQ_bind, StateT.run_bind, run_unif₁, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp]
      refine bind_congr fun u => ?_
      exact ih u L
    · have hroute : (routeA th P N (.inr (.inl (t, xs)))).run (L, ann th pk L) =
          (fun z => (z.1, (z.2, recAns th N (.inr (.inl (t, xs))) z.1 (ann th pk L)))) <$>
            routeStep th P N (.inr (.inl (t, xs))) L := rfl
      have horc : SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk (.inr (.inl (t, xs))) =
          SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone th N) pk (t, xs) := rfl
      rw [hroute, horc]
      by_cases hc : N ≤ L.length ∨ t ∈ L.map Prod.fst
      · have h0 : (SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone th N) pk (t, xs)).run
            (L, []) = pure (none, (L, [])) := by
          rcases hc with hc | hc
          · exact SM_DT_TCR_challengeOracle_run_of_full hc
          · obtain ⟨e, he, het⟩ := List.mem_map.1 hc
            exact SM_DT_TCR_challengeOracle_run_of_reused e.2 (by rw [← het]; exact he)
        have h1 : routeStep th P N (.inr (.inl (t, xs))) L = pure (none, L) := by
          simp only [routeStep, hc, ite_true]
        rw [h0, h1]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        exact ih none L
      · have hlt : L.length < N := by omega
        have hfr : t ∉ L.map Prod.fst := fun h => hc (Or.inr h)
        have h0 : (SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone th N) pk (t, xs)).run
            (L, []) = pure (some (th.eval pk t xs), (L ++ [(t, xs)], [])) :=
          SM_DT_TCR_challengeOracle_run_of_fresh hlt
            ⟨fun ⟨e, he, het⟩ => hfr (het ▸ List.mem_map_of_mem he), by simp⟩
        have hrec : recAns th N (.inr (.inl (t, xs))) (some (th.eval pk t xs)) (ann th pk L) =
            ann th pk (L ++ [(t, xs)]) := ann_append th pk L (t, xs)
        rw [h0]
        by_cases hP : P xs
        · have h1 : routeStep th P N (.inr (.inl (t, xs))) L = (fun r => (r, L ++ [(t, xs)])) <$>
              liftM ((spec₁ th P N).query (.inr (.inl (t, ⟨xs, hP⟩)))) := by
            simp only [routeStep, hc, hP, ite_false, dite_true]
            rfl
          have h2 : (simulateQ (SM_DT_TCR_oracles (classProblem th P N) pk)
              (liftM ((spec₁ th P N).query (.inr (.inl (t, ⟨xs, hP⟩)))))).run (gState P L) =
              pure (some (th.eval pk t xs), gState P (L ++ [(t, xs)])) := by
            rw [simulateQ_spec_query]
            have : SM_DT_TCR_oracles (classProblem th P N) pk (.inr (.inl (t, ⟨xs, hP⟩))) =
                SM_DT_TCR_challengeOracle (classProblem th P N) pk (t, ⟨xs, hP⟩) := rfl
            rw [this]
            have hlt' : (classTargets P L).length < (classProblem th P N).numTargets :=
              lt_of_le_of_lt (classTargets_length_le P L) hlt
            rw [gState, SM_DT_TCR_challengeOracle_run_of_fresh hlt' (fresh_gState P hfr), gState,
              classTargets_append_in P L t xs hP, otherTweaks_append_in P L t xs hP]
            rfl
          rw [h1]
          simp only [pure_bind, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
            Function.comp, h2, simulateQ_pure, StateT.run_pure, bind_assoc]
          rw [hrec]
          exact ih _ _
        · have h1 : routeStep th P N (.inr (.inl (t, xs))) L = (fun r => (r, L ++ [(t, xs)])) <$>
              liftM ((spec₁ th P N).query (.inr (.inr ⟨(), t, xs⟩))) := by
            simp only [routeStep, hc, hP, ite_false, dite_false]
            rfl
          have h2 : (simulateQ (SM_DT_TCR_oracles (classProblem th P N) pk)
              (liftM ((spec₁ th P N).query (.inr (.inr ⟨(), t, xs⟩))))).run (gState P L) =
              pure (some (th.eval pk t xs), gState P (L ++ [(t, xs)])) := by
            rw [simulateQ_spec_query]
            have : SM_DT_TCR_oracles (classProblem th P N) pk (.inr (.inr ⟨(), t, xs⟩)) =
                collectionOracle (Q := Tweak × {xs : List Y // P xs}) Prod.fst
                  (classProblem th P N).thColl pk ⟨(), t, xs⟩ := rfl
            rw [this]
            rw [gState, collectionOracle_run_of_fresh Prod.fst _ (fresh_gState P hfr).1, gState,
              classTargets_append_out P L t xs hP, otherTweaks_append_out P L t xs hP]
            rfl
          rw [h1]
          simp only [pure_bind, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
            Function.comp, h2, simulateQ_pure, StateT.run_pure, bind_assoc]
          rw [hrec]
          exact ih _ _
    · exact q.1.elim

end Generic

/-! ## The answer-storing class adversary -/

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

attribute [local irreducible] arityTargets tcrTargets

/-- The answer store: `((tweak, input), value)` triples. -/
abbrev Store (prims : Primitives vp.params) : Type :=
  List ((prims.AdrsKey × List prims.Y) × prims.Y)

/-- A store is sound at the seed `pk` when every stored value is the hash value at `pk`. -/
def Sound (pk : prims.PkSeed) (S : Store prims) : Prop :=
  ∀ e ∈ S, e.2 = prims.Thash pk e.1.1 e.1.2

/-- **The tweakable hash of the second phase: lookup in the store, hash on a miss.**  At the
seed `pk` the store is consulted first (`List.lookup` by `(tweak, input)`); only if the pair is
not stored is `Thash` evaluated.  (At any other seed: `Thash`.) -/
def lkT (pk : prims.PkSeed) (S : Store prims) :
    prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y :=
  fun pk' key xs =>
    if pk' = pk then
      match S.lookup (key, xs) with
      | some y => y
      | none => prims.Thash pk' key xs
    else prims.Thash pk' key xs

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (S : List (α × β)) (k : α) (v : β), S.lookup k = some v → (k, v) ∈ S
  | [], _, _, h => by simp at h
  | (a, b) :: es, k, v, h => by
    by_cases hk : (k == a) = true
    · have hka : k = a := eq_of_beq hk
      subst hka
      simp only [List.lookup_cons, beq_self_eq_true] at h
      obtain rfl := Option.some.inj h
      exact List.mem_cons_self
    · simp only [List.lookup_cons, Bool.not_eq_true] at h hk
      rw [hk] at h
      exact List.mem_cons_of_mem _ (lookup_mem es k v h)

/-- **On a sound store the lookup hash IS `Thash`** (a hit returns the stored value, which is
the hash value). -/
theorem lkT_eq_of_sound (pk : prims.PkSeed) (S : Store prims) (h : Sound pk S) :
    lkT pk S = prims.Thash := by
  funext pk' key xs
  unfold lkT
  by_cases hpk : pk' = pk
  · rw [ite_eq_left hpk]
    cases hl : S.lookup (key, xs) with
    | none => rfl
    | some y =>
      have := h _ (lookup_mem S (key, xs) y hl)
      subst hpk
      exact this
  · rw [ite_eq_right hpk]

/-- The store `ann … pk L` (what phase 1 produces) is sound at `pk`. -/
theorem sound_ann (pk : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y)) :
    Sound pk (ann (thashList vp prims pkSeedDist) pk L) := by
  intro e he
  simp only [ann, List.mem_map] at he
  obtain ⟨c, -, rfl⟩ := he
  rfl

/-- **Phase 2 of `bTcrArA n A`**: phase 2 of `bTcrArM n A` (`memoForge`: `PK.root`, the
forger's run with simulated signing, verification of the forgery, collision search by tweak
lookup in `L`) in which every evaluation of the tweakable hash is `lkT pkSeed S`: a lookup in
the stored phase-1 answers, falling back to `Thash` on a miss.  `H_msg` is evaluated as before.
State `s = (tbl, (L, S))`. -/
noncomputable def storeForge (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (s : SecretTable vp prims × (List (prims.AdrsKey × List prims.Y) × Store prims))
    (pkSeed : prims.PkSeed) : ProbComp (ℕ × {xs : List prims.Y // xs.length = n}) :=
  memoForge (prims := withTH prims (lkT pkSeed s.2.2) prims.Hmsg) n
    (castForger (lkT pkSeed s.2.2) prims.Hmsg A) (s.1, s.2.1) pkSeed

/-- **On a sound store, phase 2 is phase 2 of `bTcrArM n A`** — unconditionally in `L` and in
the coverage of the store (a hit returns the hash value, a miss hashes). -/
theorem storeForge_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
    (pkSeed : prims.PkSeed) (hS : Sound pkSeed S) :
    storeForge n A (tbl, (L, S)) pkSeed = memoForge n A (tbl, L) pkSeed := by
  unfold storeForge
  dsimp only
  rw [lkT_eq_of_sound pkSeed S hS]
  rfl

/-- **The answer-storing arity-`n` SM-TCR adversary**, against the tight-cap class game.
Phase 1 is phase 1 of `bTcrArM n A` run through the recording wrapper `routeA` instead of
`TcrSplit.route`: same queries, and the state also keeps the oracle answers.  State
`(tbl, (L, S))`; phase 2 is `storeForge`. -/
noncomputable def bTcrArA (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n) where
  State := SecretTable vp prims × (List (prims.AdrsKey × List prims.Y) × Store prims)
  choose := (simulateQ (routeA (thashList vp prims pkSeedDist) (fun xs => xs.length = n)
    (tcrTargets vp)) (Lazy.bTcrS A).choose).run ([], [])
  forge := storeForge n A

theorem bTcrArA_forge (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArA n A).forge = storeForge n A := rfl

/-- The same adversary typed against the loose-cap class game (cap `tcrTargets vp`); used only
to transfer phase 1 (`TightCaps.run_recap_eq`). -/
noncomputable def bTcrArAL (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist n) where
  State := SecretTable vp prims × (List (prims.AdrsKey × List prims.Y) × Store prims)
  choose := (simulateQ (routeA (thashList vp prims pkSeedDist) (fun xs => xs.length = n)
    (tcrTargets vp)) (Lazy.bTcrS A).choose).run ([], [])
  forge := storeForge n A

/-- Phase 1 of `bTcrArA n A` is literally that of its loose-cap copy. -/
theorem bTcrArA_choose (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArA n A).choose = (bTcrArAL n A).choose := rfl

/-- Phase 1 of `bTcrArA n A` in the loose-cap class game. -/
theorem bTcrArAL_choose_run (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArAL n A).choose).run ([], []) =
      (fun tbl => ((tbl, (honestCalls tbl pk,
          ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          Lazy.sparseTable vp prims := by
  have h := choose_couplingA (fun xs : List prims.Y => xs.length = n)
    (thashList vp prims pkSeedDist) (tcrTargets vp) pk (Lazy.bTcrS A).choose []
  have h' := Lazy.bTcrS_choose_run hS A pk
  unfold thashArityProblem
  dsimp only [bTcrArAL]
  refine h.trans ?_
  refine (congrArg (· >>= _) h').trans ?_
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr fun tbl => ?_
  exact pure_bind _ _

set_option linter.constructorNameAsVariable false in
theorem bTcrArAL_within (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArAL n A).choose).run ([], [])), z.2.1.length ≤ arityTargets vp n := by
  intro z hz
  rw [bTcrArAL_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact (bTcrArS_targets hS n tbl pk).1.le

/-- **Phase 1 of `bTcrArA n A` in the tight-cap class game**: one sparse table; the game state
is that of `bTcrArM n A` (`bTcrArM_choose_run`: same targets, same collection queries); the
state handed to phase 2 is `(tbl, (L, S))` with `L = honestCalls tbl pk` and `S` = every entry
of `L` with its hash value at `pk`. -/
theorem bTcrArA_choose_run (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArA n A).choose).run ([], []) =
      (fun tbl => ((tbl, (honestCalls tbl pk,
          ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))),
        TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk))) <$>
          Lazy.sparseTable vp prims :=
  (TightCaps.run_recap_eq (thashArityProblem vp prims pkSeedDist n) (arityTargets vp n)
    (arityTargets_le_tcrTargets vp n) pk (bTcrArAL n A).choose ([], [])
    (bTcrArAL_within hS n A pk)).trans (bTcrArAL_choose_run hS n A pk)

/-- **Targets and collection queries of `bTcrArA n A`** in the tight-cap class game: exactly
those of `bTcrArM n A` — `arityTargets vp n` targets in every run, targets plus collection
queries are the `tcrTargets vp` hash calls of the key structure. -/
theorem bTcrArA_phase1 (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    Resources2.TcrPhase1Counts (bTcrArA n A) (arityTargets vp n) (tcrTargets vp) :=
  Resources2.tcrPhase1Counts_of_run _ _ _ (Lazy.sparseTable vp prims)
    (fun pk tbl => ((tbl, (honestCalls tbl pk,
        ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))),
      TcrSplit.gState (fun xs => xs.length = n) (honestCalls tbl pk)))
    (fun pk => bTcrArA_choose_run hS n A pk)
    (fun pk tbl => ⟨(bTcrArS_targets hS n tbl pk).1, (bTcrArS_targets hS n tbl pk).2.1⟩)

set_option linter.constructorNameAsVariable false in
/-- **The state handed to phase 2**: `(tbl, (L, S))` with `L = honestCalls tbl pk`
(`tcrTargets vp` entries, distinct tweaks) and `S` the entries of `L` with their hash values at
`pk` (one stored answer per entry; sound). -/
theorem bTcrArA_state (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArA n A).choose).run ([], [])),
      ∃ tbl : SecretTable vp prims,
        z.1 = (tbl, (honestCalls tbl pk,
          ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk))) ∧
        (honestCalls tbl pk).length = tcrTargets vp ∧
        (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)).length = tcrTargets vp ∧
        Sound pk (ann (thashList vp prims pkSeedDist) pk (honestCalls tbl pk)) := by
  intro z hz
  rw [bTcrArA_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact ⟨tbl, rfl, (honestCalls_nodup_length hS tbl pk).2,
    by simp [ann, (honestCalls_nodup_length hS tbl pk).2], sound_ann pk _⟩

/-- Phase 2 agrees with `bTcrArM n A` on every state with a sound store. -/
theorem bTcrArA_forge_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (L : List (prims.AdrsKey × List prims.Y)) (S : Store prims)
    (pkSeed : prims.PkSeed) (hS : Sound pkSeed S) :
    (bTcrArA n A).forge (tbl, (L, S)) pkSeed = (bTcrArM n A).forge (tbl, L) pkSeed :=
  storeForge_eq n A tbl L S pkSeed hS

/-- **The experiments are equal**: `bTcrArA n A` and `bTcrArM n A` in the tight-cap class
game. -/
theorem bTcrArA_experiment_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Experiment (bTcrArA n A) = SM_DT_TCR_Experiment (bTcrArM n A) := by
  unfold SM_DT_TCR_Experiment
  refine bind_congr fun pk => ?_
  refine (congrArg (· >>= _) (bTcrArA_choose_run hS n A pk)).trans ?_
  refine Eq.trans ?_ (congrArg (· >>= _) (bTcrArM_choose_run hS n A pk)).symm
  refine (bind_map_left _ _ _).trans (Eq.trans ?_ (bind_map_left _ _ _).symm)
  refine bind_congr fun tbl => ?_
  exact congrArg (· >>= _) (bTcrArA_forge_eq n A tbl _ _ pk (sound_ann pk _))

/-- **Equal advantages**: `Adv(bTcrArA n A) = Adv(bTcrArM n A)`. -/
theorem bTcrArA_advantage_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrArA n A) = SM_DT_TCR_Advantage (bTcrArM n A) := by
  unfold SM_DT_TCR_Advantage
  rw [bTcrArA_experiment_eq hS n A]

/-- `Adv(bTcrArA n A) = Adv(bTcrArST n A)` (the adversary of the `_tight` headline). -/
theorem bTcrArA_advantage_eq_tight (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrArA n A) = SM_DT_TCR_Advantage (bTcrArST n A) :=
  (bTcrArA_advantage_eq hS n A).trans (bTcrArM_advantage_eq hS n A)

end Open

#print axioms Open.choose_couplingA
#print axioms Open.lkT_eq_of_sound
#print axioms Open.storeForge_eq
#print axioms Open.bTcrArA_choose_run
#print axioms Open.bTcrArA_experiment_eq
#print axioms Open.bTcrArA_phase1
#print axioms Open.bTcrArA_state
#print axioms Open.bTcrArA_advantage_eq
#print axioms Open.bTcrArA_advantage_eq_tight
#print axioms Open.bTcrArA
#print axioms Open.storeForge

end Reduction
