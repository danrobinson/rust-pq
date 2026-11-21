import Ideal.Core.LazyLemmas
import Ideal.Core.HPBasic
import VCVio.EvalDist.EvalDistEq

/-!
# Game-independent lemmas about hidden inputs in the lazy ideal game

In the ideal (hidden-prefix) game a challenger may evaluate the hash at a secret input `x`:
it reads the private-row cell `cell k x` (fresh, because its key `k`, a tweak, is fresh) and
publishes a function of the value `Y` found there.  The adversary's view then depends on `x`
only through *where* `Y` is stored.  This file provides the tools to exploit that.

* `patch c h`: the cache `c` with the hidden cells `h : Blk → Option St` laid over the private
  row table.
* `run_romImpl_patch`: a computation that never reads a hidden cell runs from `patch c h`
  exactly as from `c` (the hidden cells are carried along).
* `prT_run_romImpl_patch_le`: identical-until-bad.  A computation run from `patch c h` followed
  by a Boolean continuation returns `true` at most as often as the same computation run from
  `c` — which does not depend on `h` — followed by "`true` if a hidden cell was read, else the
  continuation on the patched final cache".
* `evalDistEq_run_of_intertwine`: a randomised state map `φ` that commutes in distribution
  with every step of two handlers commutes with whole runs (deferred sampling of the hidden
  inputs to the end of phase one).
* `potential_le_of_step`, `routeRO_potential_le`: pathwise potential bounds (used with the
  potential "probability over the hidden inputs that the cache contains a hidden cell").
* `hideDraw`, `hidMap`: an independent uniform hidden input for every recorded target, the
  hidden cells they determine, and the bounds
  `prEvent_hideDraw_cell_le` (a fixed cell is hidden with probability `≤ 1/|M'|`) and
  `prEvent_hideDraw_getElem_le` (the `j`-th hidden input is a fixed value with probability
  `≤ 1/|M'|`).
* `idealGame_eq_phases`: the ideal game as phase one, the seed, `cv`, phase two.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

section Patch

variable {St Blk : Type}

/-- The cache `c` with the hidden cells `h` laid over the private row table. -/
def patch (c : Cache St Blk) (h : Blk → Option St) : Cache St Blk :=
  QueryCache.ofFn fun
    | .inl q => c (.inl q)
    | .inr B => match h B with
      | some Y => some Y
      | none => c (.inr B)

/-- A query that is not a hidden cell. -/
def NotHidden (h : Blk → Option St) : (St × Blk) ⊕ Blk → Prop
  | .inl _ => True
  | .inr B => h B = none

/-- Some hidden cell is cached in `c`. -/
def HiddenRead (h : Blk → Option St) (c : Cache St Blk) : Prop :=
  ∃ B, (h B).isSome ∧ (c (.inr B)).isSome

@[simp] theorem patch_inl (c : Cache St Blk) (h : Blk → Option St) (q : St × Blk) :
    patch c h (.inl q) = c (.inl q) := rfl

theorem patch_inr_of_none (c : Cache St Blk) {h : Blk → Option St} {B : Blk} (hB : h B = none) :
    patch c h (.inr B) = c (.inr B) := by
  simp [patch, hB]

theorem patch_inr_of_some (c : Cache St Blk) {h : Blk → Option St} {B : Blk} {Y : St}
    (hB : h B = some Y) : patch c h (.inr B) = some Y := by
  simp [patch, hB]

theorem patch_of_notHidden (c : Cache St Blk) {h : Blk → Option St} {t : (St × Blk) ⊕ Blk}
    (ht : NotHidden h t) : patch c h t = c t := by
  rcases t with q | B
  · rfl
  · exact patch_inr_of_none c ht

@[simp] theorem patch_none (c : Cache St Blk) : patch c (fun _ => none) = c := by
  refine QueryCache.ext fun t => ?_
  rcases t with q | B <;> rfl

variable [DecidableEq St] [DecidableEq Blk]

theorem patch_cacheQuery (c : Cache St Blk) {h : Blk → Option St} {t : (St × Blk) ⊕ Blk}
    (ht : NotHidden h t) (u : (hS St Blk + tS St Blk).Range t) :
    patch (c.cacheQuery t u) h = (patch c h).cacheQuery t u := by
  refine QueryCache.ext fun s => ?_
  by_cases hs : s = t
  · subst hs
    rw [QueryCache.cacheQuery_self, patch_of_notHidden _ ht, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hs]
    rcases s with q | B
    · rw [patch_inl, patch_inl]
      exact QueryCache.cacheQuery_of_ne (t := t) c u hs
    · cases hB : h B with
      | none =>
        rw [patch_inr_of_none _ hB, patch_inr_of_none _ hB]
        exact QueryCache.cacheQuery_of_ne (t := t) c u hs
      | some Y => rw [patch_inr_of_some _ hB, patch_inr_of_some _ hB]

variable [SampleableType St]

/-- A lazy-oracle step at a cell that is not hidden commutes with the patch. -/
theorem randomOracle_run_patch (c : Cache St Blk) {h : Blk → Option St} {t : (St × Blk) ⊕ Blk}
    (ht : NotHidden h t) :
    ((hS St Blk + tS St Blk).randomOracle t).run (patch c h) =
      (fun z => (z.1, patch z.2 h)) <$> ((hS St Blk + tS St Blk).randomOracle t).run c := by
  rw [randomOracle.run_eq, randomOracle.run_eq, patch_of_notHidden c ht]
  cases c t with
  | none =>
    simp only [map_bind, map_pure]
    exact bind_congr fun u => by rw [patch_cacheQuery c ht]
  | some v => simp

theorem romImpl_run_inl (n : ℕ) (c : Cache St Blk) :
    ((hS St Blk + tS St Blk).romImpl (.inl n)).run c =
      (fun u => (u, c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp [unifFwdImpl]

theorem romImpl_run_inr (t : (St × Blk) ⊕ Blk) (c : Cache St Blk) :
    ((hS St Blk + tS St Blk).romImpl (.inr t)).run c =
      ((hS St Blk + tS St Blk).randomOracle t).run c := rfl

/-- A cached cell stays cached along a lazy-oracle run. -/
theorem isSome_of_mem_support_run_romImpl {α : Type}
    (oc : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (t : (St × Blk) ⊕ Blk)
    (c : Cache St Blk) (hc : (c t).isSome) :
    ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl oc).run c), (z.2 t).isSome := by
  refine simulateQ_run_preservesInv _ (fun c : Cache St Blk => (c t).isSome) ?_ oc c hc
  rintro (n | t') s hs z hz
  · rw [romImpl_run_inl, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · rw [romImpl_run_inr, randomOracle.run_eq] at hz
    cases h : s t' with
    | none =>
      rw [h] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact (QueryCache.isSome_cacheQuery_apply_iff s u).2 (.inr hs)
    | some v =>
      rw [h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hs

/-- **Hidden cells are carried along.**  A computation none of whose queries is a hidden cell
runs from the patched cache exactly as from the unpatched one. -/
theorem run_romImpl_patch {α : Type} (h : Blk → Option St)
    (oc : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α)
    (hoc : AllQueriesSatisfy oc fun i => match i with
      | .inr t => NotHidden h t
      | .inl _ => True) (c : Cache St Blk) :
    (simulateQ (hS St Blk + tS St Blk).romImpl oc).run (patch c h) =
      (fun z => (z.1, patch z.2 h)) <$> (simulateQ (hS St Blk + tS St Blk).romImpl oc).run c := by
  induction oc using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoc
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, map_bind]
    rcases t with n | t
    · rw [romImpl_run_inl, romImpl_run_inl, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u (hoc.2 u) c
    · rw [romImpl_run_inr, romImpl_run_inr, randomOracle_run_patch c hoc.1, bind_map_left]
      exact bind_congr fun z => ih z.1 (hoc.2 z.1) z.2

open Classical in
/-- **Identical until a hidden cell is read.**  Running `oc` from the patched cache and then a
Boolean continuation `f` returns `true` at most as often as running `oc` from the unpatched
cache — a run that does not depend on the hidden cells — and then returning `true` if a hidden
cell has been cached, and otherwise running `f` on the patched final cache. -/
theorem prT_run_romImpl_patch_le {α : Type} (h : Blk → Option St)
    (oc : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α)
    (f : α × Cache St Blk → ProbComp Bool) (c : Cache St Blk) (hc : ¬ HiddenRead h c) :
    HP.prT ((simulateQ (hS St Blk + tS St Blk).romImpl oc).run (patch c h) >>= f) ≤
      HP.prT ((simulateQ (hS St Blk + tS St Blk).romImpl oc).run c >>= fun z =>
        if HiddenRead h z.2 then pure true else f (z.1, patch z.2 h)) := by
  induction oc using OracleComp.inductionOn generalizing c with
  | pure x => simp [hc]
  | query_bind t k ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, bind_assoc, bind_assoc]
    rcases t with n | t
    · rw [romImpl_run_inl, romImpl_run_inl, bind_map_left, bind_map_left]
      exact HP.prT_bind_mono _ _ _ fun u _ => ih u c hc
    · rw [romImpl_run_inr, romImpl_run_inr]
      by_cases ht : NotHidden h t
      · rw [randomOracle_run_patch c ht, bind_map_left]
        refine HP.prT_bind_mono _ _ _ fun z hz => ih z.1 z.2 ?_
        rintro ⟨B, hB, hB'⟩
        refine hc ⟨B, hB, ?_⟩
        rcases t with q | B₀
        · rwa [row_eq_of_mem_support_randomOracle_pub q c hz] at hB'
        · have hne : B ≠ B₀ := fun e => by
            rw [e, show h B₀ = none from ht] at hB; exact absurd hB (by simp)
          rwa [(row_of_mem_support_randomOracle_row B₀ c hz).2 B hne] at hB'
      · rcases t with q | B₀
        · exact absurd trivial ht
        · refine (HP.prT_le_one _).trans (le_of_eq (HP.prT_eq_one_of_support _ ?_).symm)
          intro b hb
          rw [mem_support_bind_iff] at hb
          obtain ⟨us, hus, hb⟩ := hb
          rw [mem_support_bind_iff] at hb
          obtain ⟨z, hz, hb⟩ := hb
          have h1 := (row_of_mem_support_randomOracle_row B₀ c hus).1
          have h2 := isSome_of_mem_support_run_romImpl (k us.1) (.inr B₀) us.2
            (by rw [h1]; rfl) z hz
          have hH : HiddenRead h z.2 :=
            ⟨B₀, Option.isSome_iff_ne_none.mpr ht, h2⟩
          simp only [hH, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hb
          exact hb

omit [SampleableType St] in
theorem hiddenRead_cacheQuery_pub {h : Blk → Option St} {c : Cache St Blk} {q : St × Blk}
    {u : St} (hr : HiddenRead h (c.cacheQuery (.inl q) u)) : HiddenRead h c := by
  obtain ⟨B, hB, hB'⟩ := hr
  exact ⟨B, hB, by rwa [QueryCache.cacheQuery_of_ne (t := .inl q) c u (by simp)] at hB'⟩

omit [SampleableType St] in
theorem hiddenRead_cacheQuery_row {h : Blk → Option St} {c : Cache St Blk} {B : Blk} {u : St}
    (hr : HiddenRead h (c.cacheQuery (.inr B) u)) : HiddenRead h c ∨ (h B).isSome := by
  obtain ⟨B', hB, hB'⟩ := hr
  by_cases e : B' = B
  · exact .inr (e ▸ hB)
  · exact .inl ⟨B', hB, by
      rwa [QueryCache.cacheQuery_of_ne (t := .inr B) c u (by simpa using e)] at hB'⟩

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
/-- Phase one's `chainToT` forwards a lifted sampling computation unchanged. -/
theorem simulateQ_chainToT_liftM {α : Type} (pc : ProbComp α) :
    simulateQ (chainToT (St := St) (Blk := Blk))
        (liftM pc : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α) =
      (liftM pc : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [liftM_bind, simulateQ_bind, ih]
    congr 1

theorem run_chainRO_liftM {α : Type} (pc : ProbComp α) (c : Cache St Blk) :
    (simulateQ chainRO (liftM pc : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α)).run c =
      (·, c) <$> pc := by
  rw [← simulateQ_romImpl_chainToT, simulateQ_chainToT_liftM]
  exact simulateQ_romImpl_liftM_run pc c

/-- A public query of phase one commutes with the patch. -/
theorem chainRO_run_pub_patch (h : Blk → Option St) (q : St × Blk) (c : Cache St Blk) :
    ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run (patch c h) =
      (fun z => (z.1, patch z.2 h)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c := by
  rw [chainRO_run_pub, chainRO_run_pub]
  exact randomOracle_run_patch c (t := .inl q) trivial

/-- A chain query of phase one whose first block is not a hidden cell commutes with the
patch. -/
theorem chainRO_run_chain_patch (h : Blk → Option St) (q : Blk × List Blk) (hq : h q.1 = none)
    (c : Cache St Blk) :
    ((chainRO (St := St) (Blk := Blk)) (.inr (.inr q))).run (patch c h) =
      (fun z => (z.1, patch z.2 h)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr q))).run c := by
  have hfold : ∀ (bs : List Blk) (c₀ : St), AllQueriesSatisfy
      (bs.foldlM (m := OracleComp (unifSpec + (hS St Blk + tS St Blk)))
        (fun c b => liftM ((unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))) c₀)
      (fun (i : ℕ ⊕ ((St × Blk) ⊕ Blk)) => match i with
        | .inr t => NotHidden h t
        | .inl _ => True) := by
    intro bs
    induction bs with
    | nil => intro c₀; exact allQueriesSatisfy_pure _ _
    | cons b bs ih =>
      intro c₀
      rw [List.foldlM_cons, allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, fun u => ih u⟩
  simp only [chainRO, QueryImpl.apply_compose, chainToT]
  refine run_romImpl_patch h _ ?_ c
  rw [allQueriesSatisfy_query_bind_iff]
  exact ⟨hq, fun u => hfold _ _⟩

end Patch

/-! ## Deferred sampling: intertwining -/

section Intertwine

variable {α β γ : Type}

/-- A Boolean experiment's success probability depends only on its distribution. -/
theorem prT_congr_evalDistEq {g₁ g₂ : ProbComp Bool} (h : g₁ =ᵈ g₂) : HP.prT g₁ = HP.prT g₂ :=
  h.prEvent_eq fun b => b = true

/-- Swap two independent draws when the continuation after the first is, in distribution, a
draw of the second followed by a joint continuation. -/
theorem evalDistEq_bind_swap_of_support (mx : ProbComp α) (my : ProbComp β)
    (f : α → ProbComp γ) (g : α → β → ProbComp γ)
    (h : ∀ a ∈ support mx, f a =ᵈ my >>= fun b => g a b) :
    mx >>= f =ᵈ my >>= fun b => mx >>= fun a => g a b :=
  (EvalDistEq.bind_congr_of_support mx h).trans (EvalDistEq.bind_bind_swap mx my g)

variable {ι₀ ι₁ : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁} {σ σ' τ : Type}

/-- **Intertwining.**  `inner` (a game handler over an oracle interface) run through `outer`
is a stateful system with state `σ × τ`; `O'` is another system with state `σ'` on the same
queries, and `φ` a randomised map from the states of `O'` to those of the first system.  If
`φ` followed by a step of the first system has the same distribution as a step of `O'`
followed by `φ` (from every state satisfying an invariant `I` of `O'`), the same holds for
whole runs. -/
theorem evalDistEq_run_of_intertwine
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (outer : QueryImpl spec₁ (StateT τ ProbComp))
    (O' : QueryImpl spec₀ (StateT σ' ProbComp)) (φ : σ' → ProbComp (σ × τ)) (I : σ' → Prop)
    (hI : ∀ t s', I s' → ∀ z ∈ support ((O' t).run s'), I z.2)
    (hstep : ∀ t s', I s' →
      (φ s' >>= fun p => (simulateQ outer ((inner t).run p.1)).run p.2) =ᵈ
        ((O' t).run s' >>= fun z => φ z.2 >>= fun p => pure ((z.1, p.1), p.2)))
    (oa : OracleComp spec₀ α) (s' : σ') (hs : I s') :
    (φ s' >>= fun p => (simulateQ outer ((simulateQ inner oa).run p.1)).run p.2) =ᵈ
      ((simulateQ O' oa).run s' >>= fun z => φ z.2 >>= fun p => pure ((z.1, p.1), p.2)) := by
  induction oa using OracleComp.inductionOn generalizing s' with
  | pure x => simp
  | query_bind t k ih =>
    have e1 : (φ s' >>= fun p =>
          (simulateQ outer ((simulateQ inner (liftM (spec₀.query t) >>= k)).run p.1)).run p.2) =
        (φ s' >>= fun p => (simulateQ outer ((inner t).run p.1)).run p.2) >>= fun w =>
          (simulateQ outer ((simulateQ inner (k w.1.1)).run w.1.2)).run w.2 := by
      rw [bind_assoc]
      refine bind_congr fun p => ?_
      rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind]
    have e2 : ((O' t).run s' >>= fun z => φ z.2 >>= fun p =>
          (pure ((z.1, p.1), p.2) : ProbComp ((spec₀.Range t × σ) × τ))) >>= (fun w =>
          (simulateQ outer ((simulateQ inner (k w.1.1)).run w.1.2)).run w.2) =
        (O' t).run s' >>= fun z => φ z.2 >>= fun p =>
          (simulateQ outer ((simulateQ inner (k z.1)).run p.1)).run p.2 := by
      simp only [bind_assoc, pure_bind]
    rw [e1]
    refine ((hstep t s' hs).bind_left _).trans ?_
    rw [e2, run_simulateQ_query_bind, bind_assoc]
    exact EvalDistEq.bind_congr_of_support _ fun z hz => ih z.1 z.2 (hI t s' hs z hz)

end Intertwine

/-! ## Pathwise potential bounds -/

section Potential

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- **Potential bound.**  If a `p`-step of the handler raises the potential `Φ` of the state by
at most `ε` and no other step raises it, a computation making at most `n` `p`-queries raises
it by at most `n * ε`, on every run. -/
theorem potential_le_of_step (so : QueryImpl spec (StateT σ ProbComp)) (Φ : σ → ℝ≥0∞)
    (p : ι → Prop) [DecidablePred p] (ε : ℝ≥0∞)
    (hp : ∀ t s, p t → ∀ z ∈ support ((so t).run s), Φ z.2 ≤ Φ s + ε)
    (hnp : ∀ t s, ¬ p t → ∀ z ∈ support ((so t).run s), Φ z.2 ≤ Φ s)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) :
    ∀ z ∈ support ((simulateQ so oa).run s), Φ z.2 ≤ Φ s + n * ε := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_self_add
  | query_bind t k ih =>
    intro z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    by_cases hpt : p t
    · simp only [hpt, ↓reduceIte] at hn
      have hn0 : 0 < n := by simpa using hn.1
      refine (ih us.1 (n - 1) (hn.2 us.1) us.2 z hz).trans ?_
      refine (add_le_add_left (hp t s hpt us hus) _).trans (le_of_eq ?_)
      obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [hpt, ↓reduceIte] at hn
      exact (ih us.1 n (hn.2 us.1) us.2 z hz).trans
        (add_le_add_left (hnp t s hpt us hus) _)

variable {St Blk : Type} [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- **Phase-two potential bound.**  A potential of the cache that caching a public cell does
not raise and caching a private-row cell raises by at most `ε` is raised by at most `n * ε`
by a phase-two computation making at most `n` compression queries, on every run. -/
theorem routeRO_potential_le (IV : St) (sbSeed : Blk) (cv : St) (Φ : Cache St Blk → ℝ≥0∞)
    (ε : ℝ≥0∞)
    (hpub : ∀ (c : Cache St Blk) (q : St × Blk) (u : St), Φ (c.cacheQuery (.inl q) u) ≤ Φ c)
    (hrow : ∀ (c : Cache St Blk) (B : Blk) (u : St), Φ (c.cacheQuery (.inr B) u) ≤ Φ c + ε)
    (oa : OracleComp (unifSpec + hS St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (c : Cache St Blk) :
    ∀ z ∈ support ((simulateQ (routeRO IV sbSeed cv) oa).run c), Φ z.2 ≤ Φ c + n * ε := by
  classical
  refine potential_le_of_step _ Φ _ ε ?_ ?_ oa n hn c
  · rintro (n | q) s ht z hz
    · simp at ht
    · by_cases h1 : q = (IV, sbSeed)
      · subst h1
        rw [routeRO_run_seed, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact le_self_add
      · by_cases h2 : q.1 = cv
        · obtain ⟨c', B⟩ := q
          subst h2
          rw [routeRO_run_row _ _ _ _ _ h1] at hz
          rcases randomOracle_run_row_cases B s with ⟨v, -, h⟩ | ⟨-, h⟩
          · rw [h, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]
            exact le_self_add
          · rw [h, support_map] at hz
            obtain ⟨u, -, rfl⟩ := hz
            exact hrow s B u
        · rw [routeRO_run_pub _ _ _ _ _ h1 h2] at hz
          rcases randomOracle_run_pub_cases q s with ⟨v, -, h⟩ | ⟨-, h⟩
          · rw [h, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]
            exact le_self_add
          · rw [h, support_map] at hz
            obtain ⟨u, -, rfl⟩ := hz
            exact (hpub s q u).trans le_self_add
  · rintro (n | q) s ht z hz
    · rw [routeRO_run_inl, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact le_rfl
    · simp at ht

/-- The ideal game as phase one, the seed, `cv`, phase two. -/
theorem idealGame_eq_phases {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    idealGame IV sb seedGen prog₁ P₂ =
      (simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ chainToT prog₁)).run ∅ >>= fun z =>
        seedGen >>= fun seed => ($ᵗ St : ProbComp St) >>= fun cv =>
          (simulateQ (routeRO IV (sb seed) cv) (P₂ seed z.1)).run' z.2 := by
  unfold idealGame idealProg
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine bind_congr fun z => ?_
  rw [← StateT.run'_eq, simulateQ_bind, roSim.run'_liftM_bind]
  refine bind_congr fun seed => ?_
  rw [simulateQ_bind, roSim.run'_liftM_bind]
  refine bind_congr fun cv => ?_
  rw [simulateQ_romImpl_route]

end Potential

/-! ## Hidden inputs of a list of targets -/

section Hide

variable {St Blk κ M' : Type} [SampleableType M']

/-- An independent uniform hidden input for every recorded target `(key, value)`. -/
def hideDraw (l : List (κ × St)) : ProbComp (List (κ × M' × St)) :=
  l.mapM fun e => (fun x => (e.1, x, e.2)) <$> ($ᵗ M' : ProbComp M')

theorem hideDraw_nil : hideDraw (M' := M') ([] : List (κ × St)) = pure [] := rfl

theorem hideDraw_cons (e : κ × St) (l : List (κ × St)) :
    hideDraw (M' := M') (e :: l) =
      ($ᵗ M' : ProbComp M') >>= fun x => hideDraw l >>= fun xs => pure ((e.1, x, e.2) :: xs) := by
  simp [hideDraw]

theorem hideDraw_append_singleton (l : List (κ × St)) (e : κ × St) :
    hideDraw (M' := M') (l ++ [e]) =
      hideDraw l >>= fun xs => ($ᵗ M' : ProbComp M') >>= fun x => pure (xs ++ [(e.1, x, e.2)]) := by
  simp [hideDraw]

/-- The hidden-input list has the targets' keys and values. -/
theorem map_of_mem_support_hideDraw {l : List (κ × St)} {xs : List (κ × M' × St)}
    (h : xs ∈ support (hideDraw l)) : xs.map (fun e => (e.1, e.2.2)) = l := by
  induction l generalizing xs with
  | nil =>
    rw [hideDraw_nil, support_pure, Set.mem_singleton_iff] at h
    rw [h]; rfl
  | cons e l ih =>
    rw [hideDraw_cons, mem_support_bind_iff] at h
    obtain ⟨x, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨xs', hxs', h⟩ := h
    rw [support_pure, Set.mem_singleton_iff] at h
    rw [h, List.map_cons, ih hxs']

theorem map_fst_of_mem_support_hideDraw {l : List (κ × St)} {xs : List (κ × M' × St)}
    (h : xs ∈ support (hideDraw l)) : xs.map (fun e => e.1) = l.map Prod.fst := by
  rw [← map_of_mem_support_hideDraw h, List.map_map]
  rfl

theorem length_of_mem_support_hideDraw {l : List (κ × St)} {xs : List (κ × M' × St)}
    (h : xs ∈ support (hideDraw l)) : xs.length = l.length := by
  rw [← map_of_mem_support_hideDraw h, List.length_map]

/-- The hidden cells determined by the hidden inputs: the cell of a target's key and hidden
input holds the target's value. -/
def hidMap [DecidableEq Blk] (cell : κ → M' → Blk) (xs : List (κ × M' × St)) : Blk → Option St :=
  fun B => (xs.find? fun e => decide (cell e.1 e.2.1 = B)).map fun e => e.2.2

section HidMap

variable [DecidableEq Blk] (cell : κ → M' → Blk)

omit [SampleableType M'] in
theorem hidMap_nil : hidMap (St := St) cell [] = fun _ => none := rfl

omit [SampleableType M'] in
theorem hidMap_isSome_iff (xs : List (κ × M' × St)) (B : Blk) :
    (hidMap cell xs B).isSome ↔ ∃ e ∈ xs, cell e.1 e.2.1 = B := by
  simp [hidMap]

omit [SampleableType M'] in
theorem hidMap_eq_none_iff (xs : List (κ × M' × St)) (B : Blk) :
    hidMap cell xs B = none ↔ ∀ e ∈ xs, cell e.1 e.2.1 ≠ B := by
  simp [hidMap]

omit [SampleableType M'] in
/-- With keys recoverable from cells and pairwise distinct, a target's cell holds its value. -/
theorem hidMap_of_mem (key : Blk → κ) (hkey : ∀ k x, key (cell k x) = k)
    {xs : List (κ × M' × St)} (hnd : (xs.map fun e => e.1).Nodup) {e : κ × M' × St}
    (he : e ∈ xs) : hidMap cell xs (cell e.1 e.2.1) = some e.2.2 := by
  have hs : (hidMap cell xs (cell e.1 e.2.1)).isSome := (hidMap_isSome_iff cell xs _).2 ⟨e, he, rfl⟩
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp hs
  rw [hY]
  simp only [hidMap, Option.map_eq_some_iff] at hY
  obtain ⟨e', hfind, rfl⟩ := hY
  have hmem := List.mem_of_find?_eq_some hfind
  have hcell : cell e'.1 e'.2.1 = cell e.1 e.2.1 := by simpa using List.find?_some hfind
  have hk : e'.1 = e.1 := by rw [← hkey e'.1 e'.2.1, hcell, hkey]
  rw [List.inj_on_of_nodup_map hnd hmem he hk]

omit [SampleableType M'] in
/-- Appending a target whose cell is not yet hidden caches its value at its cell. -/
theorem patch_hidMap_append [DecidableEq St] (c : Cache St Blk) (xs : List (κ × M' × St))
    (e : κ × M' × St) (hnone : hidMap cell xs (cell e.1 e.2.1) = none) :
    patch c (hidMap cell (xs ++ [e])) =
      (patch c (hidMap cell xs)).cacheQuery (.inr (cell e.1 e.2.1)) e.2.2 := by
  refine QueryCache.ext fun s => ?_
  by_cases hs : s = .inr (cell e.1 e.2.1)
  · subst hs
    rw [QueryCache.cacheQuery_self]
    refine patch_inr_of_some c ?_
    have hf : (xs.find? fun e' => decide (cell e'.1 e'.2.1 = cell e.1 e.2.1)) = none := by
      simpa [hidMap] using hnone
    simp [hidMap, List.find?_append, hf]
  · rw [QueryCache.cacheQuery_of_ne _ _ hs]
    rcases s with q | B
    · rfl
    · have hB : cell e.1 e.2.1 ≠ B := fun h => hs (by rw [h])
      have : hidMap cell (xs ++ [e]) B = hidMap cell xs B := by
        simp [hidMap, List.find?_append, hB]
      simp only [patch, QueryCache.ofFn_apply, this]

end HidMap

variable [Fintype M']

/-- With pairwise distinct keys, the hidden input of a fixed key is a fixed value with
probability at most `1/|M'|`. -/
theorem prEvent_hideDraw_key_le (l : List (κ × St)) (hnd : (l.map Prod.fst).Nodup) (k₀ : κ)
    (x₀ : M') :
    Pr{let xs ← hideDraw (M' := M') l}[∃ e ∈ xs, e.1 = k₀ ∧ e.2.1 = x₀] ≤
      (Fintype.card M' : ℝ≥0∞)⁻¹ := by
  induction l with
  | nil =>
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun xs hxs => ?_]
    · exact zero_le
    · rw [hideDraw_nil, support_pure, Set.mem_singleton_iff] at hxs
      rw [hxs]
      simp
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [hideDraw_cons]
    by_cases hk : e.1 = k₀
    · refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _ (fun x => x = x₀) _ fun x hx => ?_).trans
        (SampleableType.prEvent_uniformSample_eq_singleton x₀).le
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun ys hys => ?_
      rw [mem_support_bind_iff] at hys
      obtain ⟨xs, hxs, hys⟩ := hys
      rw [support_pure, Set.mem_singleton_iff] at hys
      subst hys
      rintro ⟨e', he', hk', hx'⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hx hx'
      · refine hnd.1 ?_
        rw [hk, ← hk', ← map_fst_of_mem_support_hideDraw hxs]
        exact List.mem_map_of_mem he'
    · refine prEvent_bind_le_of_forall_le _ _ _ fun x => ?_
      rw [bind_pure_comp, prEvent_map]
      refine (prEvent_mono _ _ _ fun xs hxs => ?_).trans (ih hnd.2)
      obtain ⟨e', he', hk', hx'⟩ := hxs
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd hk' hk
      · exact ⟨e', he', hk', hx'⟩

/-- With keys recoverable from cells, cells injective in the hidden input and pairwise distinct
keys, a fixed cell is hidden with probability at most `1/|M'|`. -/
theorem prEvent_hideDraw_cell_le [DecidableEq Blk] (cell : κ → M' → Blk) (key : Blk → κ)
    (hkey : ∀ k x, key (cell k x) = k) (hinj : ∀ k x x', cell k x = cell k x' → x = x')
    (l : List (κ × St)) (hnd : (l.map Prod.fst).Nodup) (B : Blk) :
    Pr{let xs ← hideDraw (M' := M') l}[(hidMap cell xs B).isSome] ≤
      (Fintype.card M' : ℝ≥0∞)⁻¹ := by
  by_cases hex : ∃ x₀, cell (key B) x₀ = B
  · obtain ⟨x₀, hx₀⟩ := hex
    refine (prEvent_mono _ _ _ fun xs hxs => ?_).trans (prEvent_hideDraw_key_le l hnd (key B) x₀)
    obtain ⟨e, he, hB⟩ := (hidMap_isSome_iff cell xs B).1 hxs
    have hk : e.1 = key B := by rw [← hB, hkey]
    exact ⟨e, he, hk, hinj (key B) _ _ (by rw [hx₀, ← hk, hB])⟩
  · rw [prEvent_eq_zero_of_forall_not _ _ fun xs hxs => ?_]
    · exact zero_le
    · obtain ⟨e, he, hB⟩ := (hidMap_isSome_iff cell xs B).1 hxs
      exact hex ⟨e.2.1, by rw [← hB, hkey, hB]⟩

/-- With pairwise distinct keys, the `j`-th hidden input is a fixed value with probability at
most `1/|M'|`. -/
theorem prEvent_hideDraw_getElem_le (l : List (κ × St)) (hnd : (l.map Prod.fst).Nodup) (j : ℕ)
    (x₀ : M') :
    Pr{let xs ← hideDraw (M' := M') l}[∃ e, xs[j]? = some e ∧ e.2.1 = x₀] ≤
      (Fintype.card M' : ℝ≥0∞)⁻¹ := by
  cases hj : l[j]? with
  | none =>
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun xs hxs => ?_]
    · exact zero_le
    · rintro ⟨e, he, -⟩
      have h1 : j < xs.length := (List.getElem?_eq_some_iff.mp he).1
      rw [length_of_mem_support_hideDraw hxs] at h1
      rw [List.getElem?_eq_none_iff] at hj
      omega
  | some a =>
    refine (prEvent_mono_of_support _ _ _ fun xs hxs => ?_).trans
      (prEvent_hideDraw_key_le l hnd a.1 x₀)
    rintro ⟨e, he, hx⟩
    refine ⟨e, List.mem_of_getElem? he, ?_, hx⟩
    have h1 : (xs.map fun e => (e.1, e.2.2))[j]? = some (e.1, e.2.2) := by
      rw [List.getElem?_map, he]; rfl
    rw [map_of_mem_support_hideDraw hxs, hj] at h1
    rw [Option.some.inj h1]

end Hide

end Ideal

#print axioms Ideal.run_romImpl_patch
#print axioms Ideal.prT_run_romImpl_patch_le
#print axioms Ideal.evalDistEq_run_of_intertwine
#print axioms Ideal.potential_le_of_step
#print axioms Ideal.routeRO_potential_le
#print axioms Ideal.idealGame_eq_phases
#print axioms Ideal.hidMap_of_mem
#print axioms Ideal.patch_hidMap_append
#print axioms Ideal.prEvent_hideDraw_cell_le
#print axioms Ideal.prEvent_hideDraw_getElem_le
