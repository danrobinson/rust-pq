import Ideal.Realize.Walk
import Reduction.Open.Phase1Tcr

/-!
# The first phase of the class-TCR adversaries inside the ideal model (generic part)

* `embImpl`, `instImpl_emb`: a program without compression queries, read as a program of an
  ideal-model adversary (`unifSpec + X ↪ unifSpec + (hS St Blk + X)`); instantiating at any table
  gives the program back; it makes no compression query (`emb_noH`) and as many queries of every
  other kind (`emb_bound`).
* the class router `Reduction.Open.routeHF P N`, for ANY routed program:
  `routeHF_cap` — at most `N - |L|` game queries (challenge and collection together; the router
  stops at `N` recorded calls); `routeHF_len` — no game query on more than `B` values if the
  routed program has none; `routeHF_clamp` — then the recorded list has only entries of at most
  `B` values (in the form: filtering the final list changes nothing).
* `tcrChooseHF_len`: the key-structure walk only submits hash calls on `1`, `2`, `len` or `k`
  values.
* `experiment_map_choose`, `adv_ext`: two rewriting lemmas for `SM_DT_TCR_Experiment`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize

open Reduction Reduction.Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Embedding programs without compression queries -/

section Emb

variable {κ : Type} {X : OracleSpec κ} {α : Type}

/-- The index of a query of `unifSpec + X` inside `unifSpec + (hS St Blk + X)`. -/
def embIdx : ℕ ⊕ κ → ℕ ⊕ ((St × Blk) ⊕ κ)
  | .inl n => .inl n
  | .inr t => .inr (.inr t)

/-- Forward every query of `unifSpec + X` into `unifSpec + (hS St Blk + X)`. -/
def embImpl : QueryImpl (unifSpec + X) (OracleComp (unifSpec + (hS St Blk + X)))
  | .inl n => (liftM ((unifSpec + (hS St Blk + X)).query (.inl n)) :
      OracleComp (unifSpec + (hS St Blk + X)) _)
  | .inr t => (liftM ((unifSpec + (hS St Blk + X)).query (.inr (.inr t))) :
      OracleComp (unifSpec + (hS St Blk + X)) _)

/-- **Instantiating an embedded program at any table gives the program back.** -/
theorem instImpl_emb (g : CF St Blk) (oa : OracleComp (unifSpec + X) α) :
    simulateQ (instImpl g) (simulateQ (embImpl (X := X)) oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rcases t with n | t
    · simp [embImpl, instImpl]
    · simp [embImpl, instImpl]

/-- Queries of an embedded program: as many of each class as the program makes of the
corresponding class. -/
theorem emb_bound (p' : ℕ ⊕ ((St × Blk) ⊕ κ) → Prop) [DecidablePred p']
    (oa : OracleComp (unifSpec + X) α) (n : ℕ)
    (h : IsQueryBoundP oa (fun t => p' (embIdx t)) n) :
    IsQueryBoundP (simulateQ (embImpl (X := X)) oa) p' n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | t
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | t
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' => absurd h' ht

/-- An embedded program makes no query of a class that contains no embedded index (e.g. the
compression queries). -/
theorem emb_noH (p' : ℕ ⊕ ((St × Blk) ⊕ κ) → Prop) [DecidablePred p']
    (hp : ∀ t : ℕ ⊕ κ, ¬ p' (embIdx t)) (oa : OracleComp (unifSpec + X) α) :
    IsQueryBoundP (simulateQ (embImpl (X := X)) oa) p' 0 :=
  emb_bound p' oa 0 (IsQueryBoundP.of_imp (fun t ht => (hp t ht).elim) (isQueryBoundP_false oa 0))

end Emb

/-! ## The class router -/

section Route

variable {PkSeed Tweak Y : Type} [DecidableEq Tweak] (P : List Y → Prop) [DecidablePred P] (N : ℕ)
  {α : Type}

/-- A challenge query of the routed program on more than `B` values. -/
def bad0 {κ : Type} (B : ℕ) : ℕ ⊕ ((Tweak × List Y) ⊕ κ) → Bool
  | .inr (.inl tx) => decide (B < tx.2.length)
  | _ => false

/-- A challenge or collection query of the class game on more than `B` values. -/
def bad1 (B : ℕ) : ℕ ⊕ ((Tweak × {xs : List Y // P xs}) ⊕ ((_ : Unit) × Tweak × List Y)) → Bool
  | .inr (.inl tm) => decide (B < tm.2.1.length)
  | .inr (.inr q) => decide (B < q.2.2.length)
  | _ => false

/-- The recorded list restricted to the entries of at most `B` values. -/
def clampL (B : ℕ) (L : List (Tweak × List Y)) : List (Tweak × List Y) :=
  L.filter fun q => decide (q.2.length ≤ B)

omit [DecidableEq Tweak] in
theorem clampL_eq_self (B : ℕ) (L : List (Tweak × List Y)) (h : ∀ q ∈ L, q.2.length ≤ B) :
    clampL B L = L :=
  List.filter_eq_self.2 fun q hq => by simpa using h q hq

omit [DecidableEq Tweak] in
theorem clampL_mem (B : ℕ) (L : List (Tweak × List Y)) :
    ∀ q ∈ clampL B L, q.2.length ≤ B := fun q hq => by
  simpa using (List.mem_filter.1 hq).2

private theorem run_query_bind (t : (Spec0 PkSeed Tweak Y).Domain)
    (k : (Spec0 PkSeed Tweak Y).Range t → OracleComp (Spec0 PkSeed Tweak Y) α)
    (L : List (Tweak × List Y)) :
    (simulateQ (routeHF (PkSeed := PkSeed) P N)
        (liftM ((Spec0 PkSeed Tweak Y).query t) >>= k)).run L =
      routeStepHF P N t L >>= fun z => (simulateQ (routeHF (PkSeed := PkSeed) P N) (k z.1)).run z.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

private theorem routeStepHF_unif (n : ℕ) (L : List (Tweak × List Y)) :
    routeStepHF (PkSeed := PkSeed) P N (.inl n) L =
      (fun u => (u, L)) <$> liftM ((Spec1 Tweak Y P).query (.inl n)) := rfl

private theorem routeStepHF_chal (tw : Tweak) (xs : List Y) (L : List (Tweak × List Y)) :
    routeStepHF (PkSeed := PkSeed) P N (.inr (.inl (tw, xs))) L =
      if N ≤ L.length ∨ tw ∈ L.map Prod.fst then pure (none, L)
      else if h : P xs then
        (fun r => (r, L ++ [(tw, xs)])) <$>
          liftM ((Spec1 Tweak Y P).query (.inr (.inl (tw, ⟨xs, h⟩))))
      else
        (fun r => (r, L ++ [(tw, xs)])) <$>
          liftM ((Spec1 Tweak Y P).query (.inr (.inr ⟨(), tw, xs⟩))) := rfl

/-- **The router issues at most `N - |L|` game queries**, whatever program it routes: every
issued query is recorded, and nothing is issued once `N` calls are recorded. -/
theorem routeHF_cap (oa : OracleComp (Spec0 PkSeed Tweak Y) α) (L : List (Tweak × List Y)) :
    IsQueryBoundP ((simulateQ (routeHF (PkSeed := PkSeed) P N) oa).run L)
      (fun t => t.isRight = true) (N - L.length) := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure x => simp
  | query_bind t k ih =>
    rw [run_query_bind]
    rcases t with n | ⟨tw, xs⟩ | q
    · rw [routeStepHF_unif, bind_map_left]
      exact (isQueryBoundP_bind (p := fun t : (Spec1 Tweak Y P).Domain => t.isRight = true)
        (n := 0) (m := N - L.length)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => Bool.noConfusion h)
        fun u _ => ih u L).mono (by omega)
    · rw [routeStepHF_chal]
      by_cases h1 : N ≤ L.length ∨ tw ∈ L.map Prod.fst
      · rw [ite_eq_left h1, pure_bind]
        exact ih _ _
      · rw [ite_eq_right h1]
        have hlt : L.length < N := by
          by_contra hc
          exact h1 (Or.inl (Nat.le_of_not_lt hc))
        by_cases h2 : P xs
        · rw [dite_eq_left h2, bind_map_left]
          refine (isQueryBoundP_bind (p := fun t : (Spec1 Tweak Y P).Domain => t.isRight = true)
            (n := 1) (m := N - (L ++ [(tw, xs)]).length)
            ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
            fun r _ => ih r (L ++ [(tw, xs)])).mono ?_
          simp only [List.length_append, List.length_singleton]
          omega
        · rw [dite_eq_right h2, bind_map_left]
          refine (isQueryBoundP_bind (p := fun t : (Spec1 Tweak Y P).Domain => t.isRight = true)
            (n := 1) (m := N - (L ++ [(tw, xs)]).length)
            ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
            fun r _ => ih r (L ++ [(tw, xs)])).mono ?_
          simp only [List.length_append, List.length_singleton]
          omega
    · exact q.1.elim

/-- **The router issues no game query on more than `B` values**, if the routed program submits
no hash call on more than `B` values. -/
theorem routeHF_len (B : ℕ) (oa : OracleComp (Spec0 PkSeed Tweak Y) α)
    (h : IsQueryBoundP oa (fun t => bad0 B t = true) 0) (L : List (Tweak × List Y)) :
    IsQueryBoundP ((simulateQ (routeHF (PkSeed := PkSeed) P N) oa).run L)
      (fun t => bad1 P B t = true) 0 := by
  refine qb_simulateQ_run_zero (fun t ht s => ?_) h L
  show IsQueryBoundP (routeStepHF P N t s) _ 0
  rcases t with n | ⟨tw, xs⟩ | q
  · rw [routeStepHF_unif, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [bad1] at h
  · have hxs : xs.length ≤ B := by
      simp only [bad0, decide_eq_true_eq, not_lt] at ht
      exact ht
    rw [routeStepHF_chal]
    by_cases h1 : N ≤ s.length ∨ tw ∈ s.map Prod.fst
    · rw [ite_eq_left h1]
      exact isQueryBoundP_pure _ _ _
    · rw [ite_eq_right h1]
      by_cases h2 : P xs
      · rw [dite_eq_left h2, isQueryBoundP_map_iff]
        exact (isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp only [bad1, decide_eq_true_eq] at h
          omega
      · rw [dite_eq_right h2, isQueryBoundP_map_iff]
        exact (isQueryBoundP_query_iff _ _ _).2 fun h => by
          simp only [bad1, decide_eq_true_eq] at h
          omega
  · exact q.1.elim

/-- **The recorded list has only entries of at most `B` values**, if the routed program submits
no hash call on more than `B` values and the initial list has none: restricting the final list
to such entries changes nothing. -/
theorem routeHF_clamp (B : ℕ) (oa : OracleComp (Spec0 PkSeed Tweak Y) α)
    (h : IsQueryBoundP oa (fun t => bad0 B t = true) 0) (L : List (Tweak × List Y))
    (hL : ∀ q ∈ L, q.2.length ≤ B) :
    (fun z : α × List (Tweak × List Y) => (z.1, clampL B z.2)) <$>
        (simulateQ (routeHF (PkSeed := PkSeed) P N) oa).run L =
      (simulateQ (routeHF (PkSeed := PkSeed) P N) oa).run L := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, clampL_eq_self B L hL]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ bad0 B t = true := h.1.resolve_right (Nat.lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (fun t => bad0 B t = true) 0 := fun u => by
      simpa [ht] using h.2 u
    rw [run_query_bind, map_bind]
    rcases t with n | ⟨tw, xs⟩ | q
    · rw [routeStepHF_unif]
      simp only [bind_map_left]
      exact bind_congr fun u => ih u (hk u) L hL
    · have hxs : xs.length ≤ B := by
        simp only [bad0, decide_eq_true_eq, not_lt] at ht
        exact ht
      have hL' : ∀ q ∈ L ++ [(tw, xs)], q.2.length ≤ B := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hL q hq
        · rw [List.mem_singleton.1 hq]
          exact hxs
      rw [routeStepHF_chal]
      by_cases h1 : N ≤ L.length ∨ tw ∈ L.map Prod.fst
      · simp only [ite_eq_left h1, pure_bind]
        exact ih _ (hk _) L hL
      · simp only [ite_eq_right h1]
        by_cases h2 : P xs
        · simp only [dite_eq_left h2, bind_map_left]
          exact bind_congr fun u => ih u (hk u) _ hL'
        · simp only [dite_eq_right h2, bind_map_left]
          exact bind_congr fun u => ih u (hk u) _ hL'
    · exact q.1.elim

end Route

/-! ## The key-structure walk -/

section Choose

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- **The key-structure walk only submits hash calls on `1`, `2`, `len` or `k` values.** -/
theorem tcrChooseHF_len (B : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B) :
    IsQueryBoundP (tcrChooseHF vp prims)
      (fun t => bad0 (Tweak := prims.AdrsKey) (Y := prims.Y) B t = true)
      0 := by
  have h1 : IsQueryBoundP (monadLift (Lazy.sparseTable vp prims) :
      OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims))
      (fun t => bad0 (Tweak := prims.AdrsKey) (Y := prims.Y) B t = true)
      0 :=
    IsQueryBoundP.of_imp (fun t ht => by
        rcases t with n | t
        · exact Bool.noConfusion ht
        · rfl)
      (isQueryBoundP_liftM_isRight (Lazy.sparseTable vp prims))
  have h2 : ∀ (key : prims.AdrsKey) (xs : List prims.Y), OkLen vp xs →
      IsQueryBoundP (do
        let r ← ((Spec0 prims.PkSeed prims.AdrsKey prims.Y).query (Sum.inr (Sum.inl (key, xs))) :
          OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (Option prims.Y))
        pure (r.getD default))
      (fun t => bad0 (Tweak := prims.AdrsKey) (Y := prims.Y) B t = true)
      0 := by
    intro key xs hx
    refine isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
      fun r => isQueryBoundP_pure _ _ _
    have := hB xs hx
    simp only [bad0, decide_eq_true_eq] at h
    omega
  have h3 : ∀ tbl : SecretTable vp prims, IsQueryBoundP (structureVia (vp := vp) (prims := prims)
      (fun key xs => do
        let r ← ((Spec0 prims.PkSeed prims.AdrsKey prims.Y).query (Sum.inr (Sum.inl (key, xs))) :
          OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (Option prims.Y))
        pure (r.getD default))
      (fun a => pure (secretOf vp prims tbl a)))
      (fun t => bad0 (Tweak := prims.AdrsKey) (Y := prims.Y) B t = true) 0 := fun tbl =>
    np_structureVia _ h2 fun a => isQueryBoundP_pure _ _ _
  unfold tcrChooseHF
  refine isQueryBoundP_bind_zero _ _ h1 fun tbl => ?_
  refine isQueryBoundP_bind_zero _ _ ?_ fun _ => isQueryBoundP_pure _ _ _
  trace_state
  sorry
end Choose
end Ideal.Realize
