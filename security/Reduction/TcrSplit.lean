import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# Splitting SM-TCR on a variable-arity hash into per-class SM-TCR games (generic)

Let `th` be a tweakable hash with message type `List Y` (all arities at once) and
`prob = .standalone th N` the stand-alone SM-TCR problem on it, where a collision between two
messages of *different* arity also wins.  For a class of messages `P : List Y → Prop` (for
instance `fun xs => xs.length = n`) define

* `classHash th P` — `th` restricted to messages in `P` (message type `{xs // P xs}`);
* `classProblem th P N` — SM-TCR on `classHash th P` with the *whole* `th` as collection
  (`collOf th`) and the same cap `N`: the paper's per-function game, in which the other members
  of the collection can be evaluated at the hidden seed at non-target tweaks;
* `restrict P d B` — the explicit adversary against `classProblem th P N` obtained from an
  arbitrary adversary `B` against `prob`.  It runs `B.choose` once, keeps the list `L` of
  `B`'s accepted targets, answers a target query that `B`'s own game would refuse with `none`
  (without querying), forwards an accepted query in `P` to its challenge oracle and any other
  accepted query to the collection oracle; then runs `B.forge` once and, if `B`'s answer `(j, m)`
  has `m` and the `j`-th target in `P`, outputs `m` with the translated index (`classIdx`: number
  of class-`P` targets before position `j`), and otherwise gives up (out-of-range index).
  No search, no enumeration, no choice.

Main results.

* `advantage_eq_raw`, `restrict_advantage_eq`: with `raw B` the common experiment
  (seed, `B.choose` in `B`'s own game, `B.forge`),
  `Adv(B) = Pr[win B]` and `Adv_P(restrict P d B) = Pr[win B with both messages in P]` —
  an **equality**: the restricted adversary wins exactly when `B` wins by a collision inside the
  class.
* `advantage_le_sum_add_cross`: for a finite family of classes,
  `Adv(B) ≤ Σ_i Adv_{P i}(restrict (P i) (d i) B) + Pr[B wins by a collision in no class]`.
* `prEvent_le_sum_restrict`: any event that implies "B wins by a collision in some class" has
  probability at most `Σ_i Adv_{P i}(restrict (P i) (d i) B)`.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open OracleComp OracleSpec ENNReal MeasureTheory

namespace Reduction.TcrSplit

open TweakableHash

variable {PkSeed Tweak Y : Type}

/-! ## The per-class games -/

/-- `th` restricted to the messages in `P`. -/
def classHash (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) :
    TweakableHash PkSeed Tweak {xs : List Y // P xs} Y where
  seedGen := th.seedGen
  eval := fun pk t m => th.eval pk t m.1

/-- The whole variable-arity hash as a one-member collection. -/
def collOf (th : TweakableHash PkSeed Tweak (List Y) Y) :
    TweakableHashCollection Unit PkSeed Tweak Y where
  Msg := fun _ => List Y
  eval := fun _ => th.eval

/-- SM-TCR on the class `P` of `th`, with `th` as collection and cap `N`. -/
def classProblem (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) (N : ℕ) :
    SM_DT_TCR_Problem Unit PkSeed Tweak {xs : List Y // P xs} Y where
  th := classHash th P
  thColl := collOf th
  numTargets := N

/-- Oracle interface of the stand-alone game on `th`. -/
abbrev spec₀ (th : TweakableHash PkSeed Tweak (List Y) Y) (N : ℕ) :=
  unifSpec + (SM_DT_TCR_challengeSpec Tweak (List Y) Y +
    collectionSpec (SM_DT_TCR_Problem.standalone th N).thColl)

/-- Oracle interface of the class game. -/
abbrev spec₁ (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) (N : ℕ) :=
  unifSpec + (SM_DT_TCR_challengeSpec Tweak {xs : List Y // P xs} Y +
    collectionSpec (classProblem th P N).thColl)

/-! ## The restricted adversary -/

section Restrict

variable [DecidableEq Tweak]

/-- One step of the wrapper: `L` is the list of targets `B`'s own game has accepted so far. -/
def routeStep (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) [DecidablePred P]
    (N : ℕ) : (q : (spec₀ th N).Domain) → List (Tweak × List Y) →
      OracleComp (spec₁ th P N) ((spec₀ th N).Range q × List (Tweak × List Y))
  | .inl q, L => (fun u => (u, L)) <$> liftM ((spec₁ th P N).query (.inl q))
  | .inr (.inl (t, xs)), L =>
      if N ≤ L.length ∨ t ∈ L.map Prod.fst then pure (none, L)
      else if h : P xs then
        (fun r => (r, L ++ [(t, xs)])) <$> liftM ((spec₁ th P N).query (.inr (.inl (t, ⟨xs, h⟩))))
      else
        (fun r => (r, L ++ [(t, xs)])) <$> liftM ((spec₁ th P N).query (.inr (.inr ⟨(), t, xs⟩)))
  | .inr (.inr q), _ => q.1.elim

/-- The wrapper as a stateful handler. -/
def route (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) [DecidablePred P]
    (N : ℕ) : QueryImpl (spec₀ th N)
      (StateT (List (Tweak × List Y)) (OracleComp (spec₁ th P N))) :=
  fun q => StateT.mk (routeStep th P N q)

/-- Position of target `j` among the class-`P` targets: the number of class-`P` targets before
it. -/
def classIdx (P : List Y → Prop) [DecidablePred P] (L : List (Tweak × List Y)) (j : ℕ) : ℕ :=
  ((L.take j).filter fun q => decide (P q.2)).length

/-- **The class-`P` adversary derived from `B`.**  `d` is any message of the class (returned when
`B`'s answer is not in the class; such an answer never wins the class game). -/
def restrict {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ} (P : List Y → Prop)
    [DecidablePred P] (d : {xs : List Y // P xs})
    (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    SM_DT_TCR_Adversary (classProblem th P N) where
  State := B.State × List (Tweak × List Y)
  choose := (simulateQ (route th P N) B.choose).run []
  forge := fun s pk => do
    let jm ← B.forge s.1 pk
    pure (match s.2[jm.1]? with
      | some q => if h : P q.2 ∧ P jm.2 then (classIdx P s.2 jm.1, ⟨jm.2, h.2⟩)
          else (s.2.length, d)
      | none => (s.2.length, d))

/-- The class-`P` targets among `L`. -/
def classTargets (P : List Y → Prop) [DecidablePred P] (L : List (Tweak × List Y)) :
    List (Tweak × {xs : List Y // P xs}) :=
  L.filterMap fun q => if h : P q.2 then some (q.1, ⟨q.2, h⟩) else none

/-- The tweaks of the other targets among `L` (sent to the collection oracle). -/
def otherTweaks (P : List Y → Prop) [DecidablePred P] (L : List (Tweak × List Y)) : List Tweak :=
  (L.filter fun q => decide (¬ P q.2)).map Prod.fst

/-- State of the class game after the wrapper has accepted `L`. -/
def gState (P : List Y → Prop) [DecidablePred P] (L : List (Tweak × List Y)) :
    SM_DT_TCR_State Tweak {xs : List Y // P xs} :=
  (classTargets P L, otherTweaks P L)

variable (P : List Y → Prop) [DecidablePred P]

theorem classTargets_append_in (L : List (Tweak × List Y)) (t : Tweak) (xs : List Y) (h : P xs) :
    classTargets P (L ++ [(t, xs)]) = classTargets P L ++ [(t, ⟨xs, h⟩)] := by
  simp [classTargets, List.filterMap_append, h]

theorem classTargets_append_out (L : List (Tweak × List Y)) (t : Tweak) (xs : List Y)
    (h : ¬ P xs) : classTargets P (L ++ [(t, xs)]) = classTargets P L := by
  simp [classTargets, List.filterMap_append, h]

theorem otherTweaks_append_in (L : List (Tweak × List Y)) (t : Tweak) (xs : List Y) (h : P xs) :
    otherTweaks P (L ++ [(t, xs)]) = otherTweaks P L := by
  simp [otherTweaks, List.filter_append, h]

theorem otherTweaks_append_out (L : List (Tweak × List Y)) (t : Tweak) (xs : List Y)
    (h : ¬ P xs) : otherTweaks P (L ++ [(t, xs)]) = otherTweaks P L ++ [t] := by
  simp [otherTweaks, List.filter_append, h]

theorem classTargets_length_le (L : List (Tweak × List Y)) :
    (classTargets P L).length ≤ L.length :=
  List.length_filterMap_le _ _

theorem mem_classTargets_fst {L : List (Tweak × List Y)} {e : Tweak × {xs : List Y // P xs}}
    (he : e ∈ classTargets P L) : e.1 ∈ L.map Prod.fst := by
  simp only [classTargets, List.mem_filterMap] at he
  obtain ⟨q, hq, hqe⟩ := he
  split_ifs at hqe with h
  obtain rfl := Option.some.inj hqe
  exact List.mem_map_of_mem hq

theorem mem_otherTweaks {L : List (Tweak × List Y)} {t : Tweak} (ht : t ∈ otherTweaks P L) :
    t ∈ L.map Prod.fst := by
  simp only [otherTweaks, List.mem_map, List.mem_filter] at ht
  obtain ⟨q, ⟨hq, -⟩, rfl⟩ := ht
  exact List.mem_map_of_mem hq

/-- A tweak not yet used by `B` is fresh in the class game. -/
theorem fresh_gState {L : List (Tweak × List Y)} {t : Tweak} (ht : t ∉ L.map Prod.fst) :
    TweakFresh Prod.fst (classTargets P L) (otherTweaks P L) t :=
  ⟨fun ⟨_, he, het⟩ => ht (het ▸ mem_classTargets_fst P he), fun h => ht (mem_otherTweaks P h)⟩

/-- Index translation: target `j` of `B`, if in the class, is target `classIdx P L j` of the
class game. -/
theorem classTargets_getElem? (L : List (Tweak × List Y)) (j : ℕ) (t : Tweak) (xs : List Y)
    (h : P xs) (hj : L[j]? = some (t, xs)) :
    (classTargets P L)[classIdx P L j]? = some (t, ⟨xs, h⟩) := by
  induction L generalizing j with
  | nil => simp at hj
  | cons q L ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp [classTargets, classIdx, h]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := ih j hj
      by_cases hq : P q.2
      · simpa [classTargets, classIdx, hq] using this
      · simpa [classTargets, classIdx, hq] using this

/-! ## Coupling of the two selection phases -/

section Coupling

variable (th : TweakableHash PkSeed Tweak (List Y) Y) (N : ℕ) (pk : PkSeed)

theorem run_unif₁ (n : ℕ) (σ : SM_DT_TCR_State Tweak {xs : List Y // P xs}) :
    (simulateQ (SM_DT_TCR_oracles (classProblem th P N) pk)
      (liftM ((spec₁ th P N).query (.inl n)))).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  rw [simulateQ_spec_query]
  simp [SM_DT_TCR_oracles]

theorem run_unif₀ (n : ℕ) (σ : SM_DT_TCR_State Tweak (List Y)) :
    (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk (.inl n)).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [SM_DT_TCR_oracles]

theorem choose_coupling {α : Type} (oa : OracleComp (spec₀ th N) α)
    (L : List (Tweak × List Y)) :
    (simulateQ (SM_DT_TCR_oracles (classProblem th P N) pk)
        ((simulateQ (route th P N) oa).run L)).run (gState P L) =
      (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk) oa).run (L, []) >>=
        fun z => pure ((z.1, z.2.1), gState P z.2.1) := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases q with n | ⟨t, xs⟩ | q
    · rw [run_unif₀]
      have h1 : (route th P N (.inl n)).run L =
          (fun u => (u, L)) <$> liftM ((spec₁ th P N).query (.inl n)) := rfl
      rw [h1]
      simp only [simulateQ_bind, StateT.run_bind, run_unif₁, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp]
      refine bind_congr fun u => ?_
      exact ih u L
    · have hroute : (route th P N (.inr (.inl (t, xs)))).run L =
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
        simp only [pure_bind, simulateQ_pure, StateT.run_pure]
        exact ih none L
      · have hlt : L.length < N := by omega
        have hfr : t ∉ L.map Prod.fst := fun h => hc (Or.inr h)
        have h0 : (SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone th N) pk (t, xs)).run
            (L, []) = pure (some (th.eval pk t xs), (L ++ [(t, xs)], [])) :=
          SM_DT_TCR_challengeOracle_run_of_fresh hlt
            ⟨fun ⟨e, he, het⟩ => hfr (het ▸ List.mem_map_of_mem he), by simp⟩
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
            Function.comp, h2, simulateQ_pure, StateT.run_pure]
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
            Function.comp, h2, simulateQ_pure, StateT.run_pure]
          exact ih _ _
    · exact q.1.elim

end Coupling

/-! ## The games -/

section Game

variable [DecidableEq Y] {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ}

/-- Outcome of the common experiment: seed, accepted targets of `B`, answer `(j, m)` of `B`. -/
abbrev Raw (PkSeed Tweak Y : Type) : Type := PkSeed × List (Tweak × List Y) × (ℕ × List Y)

/-- The common experiment: `B` in its own (stand-alone, all-arity) SM-TCR game. -/
def raw (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    ProbComp (Raw PkSeed Tweak Y) := do
  let pk ← th.seedGen
  let z ← (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk) B.choose).run
    ([], [])
  let jm ← B.forge z.1 pk
  pure (pk, z.2.1, jm)

/-- `B` wins its own game. -/
def win (th : TweakableHash PkSeed Tweak (List Y) Y) (r : Raw PkSeed Tweak Y) : Bool :=
  match r.2.1[r.2.2.1]? with
  | none => false
  | some (t, mj) => decide (r.2.2.2 ≠ mj ∧ th.eval r.1 t r.2.2.2 = th.eval r.1 t mj)

/-- `B` wins its own game by a collision between two messages of the class `P`. -/
def winIn (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop) [DecidablePred P]
    (r : Raw PkSeed Tweak Y) : Bool :=
  match r.2.1[r.2.2.1]? with
  | none => false
  | some (t, mj) =>
      decide (P mj ∧ P r.2.2.2 ∧ r.2.2.2 ≠ mj ∧ th.eval r.1 t r.2.2.2 = th.eval r.1 t mj)

theorem winIn_le_win (r : Raw PkSeed Tweak Y) (h : winIn th P r = true) : win th r = true := by
  unfold winIn at h
  unfold win
  split at h
  · exact absurd h (by simp)
  · rename_i t mj heq
    simp only [decide_eq_true_eq] at h ⊢
    exact h.2.2

theorem experiment_eq_raw (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    SM_DT_TCR_Experiment B = win th <$> raw B := by
  unfold SM_DT_TCR_Experiment raw
  simp only [map_bind, map_pure]
  refine bind_congr fun pk => bind_congr fun z => bind_congr fun jm => ?_
  obtain ⟨s, L, tw⟩ := z
  obtain ⟨j, m⟩ := jm
  simp only [win]
  cases L[j]? with
  | none => rfl
  | some q => rfl

/-- The winning condition of the class game at the restricted adversary's output, as a function
of `B`'s run. -/
theorem class_win_eq (d : {xs : List Y // P xs}) (pk : PkSeed) (L : List (Tweak × List Y))
    (j : ℕ) (m : List Y) :
    (match (classTargets P L)[(match L[j]? with
        | some q => if h : P q.2 ∧ P m then (classIdx P L j, (⟨m, h.2⟩ : {xs : List Y // P xs}))
            else (L.length, d)
        | none => (L.length, d)).1]? with
      | none => false
      | some (t, mj) =>
          decide ((match L[j]? with
            | some q => if h : P q.2 ∧ P m then (classIdx P L j, (⟨m, h.2⟩ : {xs : List Y // P xs}))
                else (L.length, d)
            | none => (L.length, d)).2 ≠ mj ∧
            (classHash th P).eval pk t (match L[j]? with
            | some q => if h : P q.2 ∧ P m then (classIdx P L j, (⟨m, h.2⟩ : {xs : List Y // P xs}))
                else (L.length, d)
            | none => (L.length, d)).2 = (classHash th P).eval pk t mj)) =
      winIn th P (pk, L, (j, m)) := by
  have hout : (classTargets P L)[L.length]? = none :=
    List.getElem?_eq_none (classTargets_length_le P L)
  simp only [winIn]
  cases hq : L[j]? with
  | none => simp only [hout]
  | some q =>
    obtain ⟨t, mj⟩ := q
    by_cases h : P mj ∧ P m
    · simp only [dif_pos h, classTargets_getElem? P L j t mj h.1 hq]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, classHash, ne_eq, Subtype.mk.injEq]
      exact ⟨fun h' => ⟨h.1, h.2, h'.1, h'.2⟩, fun h' => ⟨h'.2.2.1, h'.2.2.2⟩⟩
    · simp only [dif_neg h, hout]
      symm
      rw [decide_eq_false_iff_not]
      exact fun h' => h ⟨h'.1, h'.2.1⟩

theorem restrict_experiment_eq (d : {xs : List Y // P xs})
    (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    SM_DT_TCR_Experiment (restrict P d B) = winIn th P <$> raw B := by
  have hcpl : ∀ pk, (simulateQ (SM_DT_TCR_oracles (classProblem th P N) pk)
      ((simulateQ (route th P N) B.choose).run [])).run ([], []) =
      (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th N) pk) B.choose).run
        ([], []) >>= fun z => pure ((z.1, z.2.1), gState P z.2.1) :=
    fun pk => choose_coupling P th N pk B.choose []
  unfold SM_DT_TCR_Experiment raw
  simp only [restrict, hcpl, map_bind, map_pure, bind_assoc, pure_bind]
  refine bind_congr fun pk => bind_congr fun z => bind_congr fun jm => ?_
  obtain ⟨s, L, tw⟩ := z
  obtain ⟨j, m⟩ := jm
  have := class_win_eq (th := th) P d pk L j m
  simp only [gState]
  rw [← this]
  split <;> rename_i hh
  · simp only [hh]
  · simp only [hh]
    rfl

/-- `Adv(B) = Pr[B wins]` over the common experiment. -/
theorem advantage_eq_raw (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    SM_DT_TCR_Advantage B = 𝒟[win th <$> raw B] {true} := by
  unfold SM_DT_TCR_Advantage
  rw [experiment_eq_raw]

/-- **The restricted adversary wins exactly when `B` wins by a collision inside the class.** -/
theorem restrict_advantage_eq (d : {xs : List Y // P xs})
    (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    SM_DT_TCR_Advantage (restrict P d B) = 𝒟[winIn th P <$> raw B] {true} := by
  unfold SM_DT_TCR_Advantage
  rw [restrict_experiment_eq]

end Game

end Restrict

/-! ## Union bound over a finite family of classes -/

section Union

variable [DecidableEq Tweak] [DecidableEq Y] {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ}
variable {κ : Type} [Fintype κ] (P : κ → List Y → Prop) [∀ i, DecidablePred (P i)]
  (d : ∀ i, {xs : List Y // P i xs})

/-- **Any event implying "`B` wins by a collision inside some class" is bounded by the sum of the
class advantages of the restricted adversaries.** -/
theorem prEvent_le_sum_restrict (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N))
    (E : Raw PkSeed Tweak Y → Bool) (hE : ∀ r, E r = true → ∃ i, winIn th (P i) r = true) :
    𝒟[E <$> raw B] {true} ≤ ∑ i, SM_DT_TCR_Advantage (restrict (P i) (d i) B) := by
  let _ : MeasurableSpace (Raw PkSeed Tweak Y) := ⊤
  simp only [restrict_advantage_eq, evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)]
  calc 𝒟[raw B] (E ⁻¹' {true})
      ≤ 𝒟[raw B] (⋃ i, winIn th (P i) ⁻¹' {true}) :=
        measure_mono fun r hr => Set.mem_iUnion.2 (hE r hr)
    _ ≤ ∑ i, 𝒟[raw B] (winIn th (P i) ⁻¹' {true}) := measure_iUnion_fintype_le _ _

/-- `B` wins its own game by a collision that lies in none of the classes (for instance between
two messages of different arity). -/
def winCross (th : TweakableHash PkSeed Tweak (List Y) Y) (r : Raw PkSeed Tweak Y) : Bool :=
  win th r && !decide (∃ i, winIn th (P i) r = true)

/-- **Split with the exact correction term.**
`Adv(B) ≤ Σ_i Adv_{P i}(restrict (P i) (d i) B) + Pr[B wins by a collision in no class]`. -/
theorem advantage_le_sum_add_cross
    (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    SM_DT_TCR_Advantage B ≤ ∑ i, SM_DT_TCR_Advantage (restrict (P i) (d i) B) +
      𝒟[winCross P th <$> raw B] {true} := by
  have h := prEvent_le_sum_restrict P d B (fun r => decide (∃ i, winIn th (P i) r = true))
    (fun r hr => by simpa using hr)
  refine le_trans ?_ (add_le_add h le_rfl)
  rw [advantage_eq_raw]
  let _ : MeasurableSpace (Raw PkSeed Tweak Y) := ⊤
  simp only [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)]
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro r hr
  by_cases hc : ∃ i, winIn th (P i) r = true
  · exact Or.inl (by simpa using hc)
  · refine Or.inr ?_
    have hw : win th r = true := hr
    simp [winCross, hw, hc]

/-- If `B` never wins by a collision outside the classes, the split has no correction term. -/
theorem advantage_le_sum_of_no_cross
    (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N))
    (h : ∀ r ∈ support (raw B), win th r = true → ∃ i, winIn th (P i) r = true) :
    SM_DT_TCR_Advantage B ≤ ∑ i, SM_DT_TCR_Advantage (restrict (P i) (d i) B) := by
  refine (advantage_le_sum_add_cross P d B).trans (le_of_eq ?_)
  have h0 : 𝒟[winCross P th <$> raw B] {true} = 0 := by
    refine evalDist.apply_eq_zero_of_disjoint_support _ (MeasurableSet.of_discrete) ?_
    intro b hb hbt
    rw [Set.mem_singleton_iff] at hbt
    subst hbt
    simp only [support_map, Set.mem_image] at hb
    obtain ⟨r, hr, hrt⟩ := hb
    simp only [winCross, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hrt
    exact hrt.2 (h r hr hrt.1)
  rw [h0, add_zero]

end Union

#print axioms choose_coupling
#print axioms restrict_advantage_eq
#print axioms prEvent_le_sum_restrict
#print axioms advantage_le_sum_add_cross
#print axioms restrict

end Reduction.TcrSplit
