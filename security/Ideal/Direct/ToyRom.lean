import Ideal.Direct.ToyDefer

/-!
# The toy game: hazards and pending charges of the deferred game's lazy tables

For a fixed list `fl` of logged adversary queries and an optional forged triple `he`, the
**hazards** of a joint cache `c` of the deferred game's two tables (`g0`, `s`) are

* `GFc`: a logged chain-block query whose input equals the (sampled) honest value there,
* `HitC`: a cached `g0` cell at a chain block whose output equals the (sampled) next honest
  value,
* `HEc`: the forged value equal to the (sampled) honest value at its position,

and the **pending charge** `Pot` is `δ` times the number of candidates whose honest value is not
yet sampled (one per logged chain query, one per cached `g0` chain cell, one for `he`), plus `κ`
times the number of logged secret-keyed queries (the secret is drawn at the very end).

`rom_step`: one lazy-table step out of a hazard-free cache raises the expected `hz` by at most
`δ` if it is a fresh `g0` chain cell and by nothing otherwise.  A fresh honest value resolves
exactly the candidates it can fire, so it is charge-neutral (`fresh_s`); a fresh `g0` chain cell
fires a hit at once or adds one pending candidate (`fresh_g`).  `rom_run_le`: the bound over a
whole program of the deferred game's tables.
-/

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Toy

namespace Params

open Classical

variable {St Blk K Y : Type} (T : Params St Blk K Y)
variable [DecidableEq St] [DecidableEq Blk] [DecidableEq Y] [Fintype St] [Fintype Blk]
  [SampleableType St]

/-- Joint cache of the deferred game's tables. -/
abbrev C2 := T.spec2.QueryCache

/-- A chain block at a position `j < w`. -/
noncomputable def chS (q : St × Blk) : Option (Fin T.m × ℕ × Y) :=
  if q.1 = T.cv then
    match T.parse q.2 with
    | .chn a j x => if j < T.w then some (a, j, x) else none
    | _ => none
  else none

theorem chS_eq_some {q : St × Blk} {a : Fin T.m} {j : ℕ} {x : Y} :
    T.chS q = some (a, j, x) ↔ q.1 = T.cv ∧ T.parse q.2 = .chn a j x ∧ j < T.w := by
  unfold chS
  by_cases hc : q.1 = T.cv
  · simp only [hc, if_true, true_and]
    rcases T.parse q.2 with ⟨a', k'⟩ | ⟨a', j', x'⟩ | _
    · simp
    · by_cases hj : j' < T.w
      · simp only [hj, if_true, Option.some.injEq, Prod.mk.injEq, Shape.chn.injEq]
        constructor
        · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl, rfl⟩, hj⟩
        · rintro ⟨⟨rfl, rfl, rfl⟩, -⟩; exact ⟨rfl, rfl, rfl⟩
      · simp only [hj, if_false]
        constructor
        · intro h; cases h
        · rintro ⟨⟨rfl, rfl, rfl⟩, h⟩; exact absurd h hj
    · simp
  · simp [hc]

/-- A secret-keyed block. -/
def isKey (q : St × Blk) : Prop := q.1 = T.cv ∧ ∃ a k, T.parse q.2 = .key a k

/-! ## Hazards and pending charges -/

/-- A logged chain query whose input is the sampled honest value. -/
def GFc (c : T.C2) (q : St × Blk) : Prop :=
  ∃ a j x, T.chS q = some (a, j, x) ∧ ∃ u, c (.inr (a, T.ix j)) = some u ∧ x = T.out u

/-- A cached `g0` chain cell whose output is the sampled next honest value. -/
def HitC (c : T.C2) (q : St × Blk) : Prop :=
  ∃ a j x, T.chS q = some (a, j, x) ∧ ∃ v u, c (.inl q) = some v ∧
    c (.inr (a, T.ix (j + 1))) = some u ∧ T.out v = T.out u

/-- The forged value is the sampled honest value at its position. -/
def HEc (he : Option (Fin T.m × ℕ × Y)) (c : T.C2) : Prop :=
  ∃ a j x, he = some (a, j, x) ∧ ∃ u, c (.inr (a, T.ix j)) = some u ∧ x = T.out u

/-- The hazard. -/
def Hz (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y)) (c : T.C2) : Prop :=
  (∃ q ∈ fl, T.GFc c q) ∨ (∃ q, T.HitC c q) ∨ T.HEc he c

/-- A pending guess candidate. -/
def pGF (c : T.C2) (q : St × Blk) : Prop :=
  ∃ a j x, T.chS q = some (a, j, x) ∧ c (.inr (a, T.ix j)) = none

/-- A pending hit candidate. -/
def pHit (c : T.C2) (q : St × Blk) : Prop :=
  ∃ a j x, T.chS q = some (a, j, x) ∧ (c (.inl q)).isSome ∧ c (.inr (a, T.ix (j + 1))) = none

/-- The forged value's candidate is pending. -/
def pHE (he : Option (Fin T.m × ℕ × Y)) (c : T.C2) : Prop :=
  ∃ a j x, he = some (a, j, x) ∧ c (.inr (a, T.ix j)) = none

/-- The pending charge. -/
noncomputable def Pot (δ κ : ℝ≥0∞) (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y))
    (c : T.C2) : ℝ≥0∞ :=
  δ * (fl.countP fun q => decide (T.pGF c q)) +
    δ * ((Finset.univ.filter fun q => T.pHit c q).card : ℕ) + δ * propInd (T.pHE he c) +
      κ * (fl.countP fun q => decide (T.isKey q))

/-- The charged lazy-table queries: fresh `g0` chain cells. -/
noncomputable def isHSF : ℕ ⊕ ((St × Blk) ⊕ T.HIdx) → Bool
  | .inr (.inl q) => (T.chS q).isSome
  | _ => false

/-! ## Counting helpers -/

theorem propInd_congr {P Q : Prop} (h : P ↔ Q) : propInd P = propInd Q := by rw [propext h]

theorem countP_split {α : Type} (l : List α) (p p₁ p₂ : α → Prop) [DecidablePred p]
    [DecidablePred p₁] [DecidablePred p₂] (h : ∀ x, p x ↔ p₁ x ∨ p₂ x) (hd : ∀ x, ¬ (p₁ x ∧ p₂ x)) :
    (l.countP fun x => decide (p x)) =
      (l.countP fun x => decide (p₁ x)) + (l.countP fun x => decide (p₂ x)) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : p₁ y
    · have : p y := (h y).2 (.inl h1)
      have h2 : ¬ p₂ y := fun h2 => hd y ⟨h1, h2⟩
      simp [this, h1, h2]; omega
    · by_cases h2 : p₂ y
      · have : p y := (h y).2 (.inr h2)
        simp [this, h1, h2]; omega
      · have : ¬ p y := fun hp => ((h y).1 hp).elim h1 h2
        simp [this, h1, h2]

theorem card_split {α : Type} [Fintype α] (p p₁ p₂ : α → Prop) [DecidablePred p]
    [DecidablePred p₁] [DecidablePred p₂] (h : ∀ x, p x ↔ p₁ x ∨ p₂ x) (hd : ∀ x, ¬ (p₁ x ∧ p₂ x)) :
    (Finset.univ.filter fun x => p x).card =
      (Finset.univ.filter fun x => p₁ x).card + (Finset.univ.filter fun x => p₂ x).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp [h x]
  · rw [Finset.disjoint_filter]; exact fun x _ h1 h2 => hd x ⟨h1, h2⟩

/-- Union bound over a list with per-element indicator bounds. -/
theorem prEvent_exists_list_le_countP {β γ : Type} (mx : ProbComp β) (l : List γ)
    (p : γ → β → Prop) (r : γ → Prop) [DecidablePred r] (δ : ℝ≥0∞)
    (h : ∀ e, Pr{let u ← mx}[p e u] ≤ δ * propInd (r e)) :
    Pr{let u ← mx}[∃ e ∈ l, p e u] ≤ δ * (l.countP fun e => decide (r e)) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    refine (prEvent_mono _ _ (fun u => p e u ∨ ∃ e' ∈ l, p e' u) fun u hu => ?_).trans
      ((prEvent_or_le _ _ _).trans ?_)
    · obtain ⟨e', he', hp⟩ := hu
      rcases List.mem_cons.mp he' with rfl | he'
      · exact .inl hp
      · exact .inr ⟨e', he', hp⟩
    · refine (add_le_add (h e) ih).trans (le_of_eq ?_)
      by_cases hr : r e
      · simp [List.countP_cons, hr, propInd, mul_add, add_comm]
      · simp [List.countP_cons, hr, propInd]

/-- Union bound over a finite type with per-element indicator bounds. -/
theorem prEvent_exists_fintype_le {β γ : Type} [Fintype γ] (mx : ProbComp β)
    (p : γ → β → Prop) (r : γ → Prop) [DecidablePred r] (δ : ℝ≥0∞)
    (h : ∀ e, Pr{let u ← mx}[p e u] ≤ δ * propInd (r e)) :
    Pr{let u ← mx}[∃ e, p e u] ≤ δ * ((Finset.univ.filter fun e => r e).card : ℕ) := by
  refine (prEvent_exists_le mx p).trans ((Finset.sum_le_sum fun e _ => h e).trans (le_of_eq ?_))
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hr : r e <;> simp [propInd, hr]

/-! ## One lazy-table step -/

variable {δ : ℝ≥0∞} (κ : ℝ≥0∞)

/-- A fresh `g0` cell: it fires a hit with probability at most `δ` if it is a chain cell whose next
honest value is sampled, else adds one pending candidate if it is a chain cell. -/
theorem fresh_g (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y)) (c : T.C2) (q : St × Blk)
    (hq : c (.inl q) = none) (hc : ¬ T.Hz fl he c) :
    ex ($ᵗ St : ProbComp St) (fun v => hz (T.Hz fl he) (T.Pot δ κ fl he)
        (c.cacheQuery (.inl q) v)) ≤
      T.Pot δ κ fl he c + (if (T.chS q).isSome then δ else 0) := by
  have hs : ∀ v i, (c.cacheQuery (.inl q) v) (.inr i) = c (.inr i) := fun v i =>
    QueryCache.cacheQuery_of_ne _ _ (by simp)
  have hg : ∀ v q', q' ≠ q → (c.cacheQuery (.inl q) v) (.inl q') = c (.inl q') := fun v q' h =>
    QueryCache.cacheQuery_of_ne _ _ (by simpa using h)
  have hgq : ∀ v, (c.cacheQuery (.inl q) v) (.inl q) = some v := fun v =>
    QueryCache.cacheQuery_self _ _ _
  set Fv : St → Prop := fun v => ∃ a j x, T.chS q = some (a, j, x) ∧ ∃ u,
    c (.inr (a, T.ix (j + 1))) = some u ∧ T.out v = T.out u with hFv
  set Nx : Prop := ∃ a j x, T.chS q = some (a, j, x) ∧ c (.inr (a, T.ix (j + 1))) = none with hNx
  refine (ex_hz_fresh_le _ _ _ _ Fv (δ * propInd (∃ a j x, T.chS q = some (a, j, x) ∧
      (c (.inr (a, T.ix (j + 1)))).isSome)) (T.Pot δ κ fl he c + δ * propInd Nx) ?_ ?_ ?_).trans ?_
  · -- a new hazard is a hit of the new cell
    intro v hv
    rcases hv with ⟨q', hq', a, j, x, hch, u, hu, hx⟩ | ⟨q', a, j, x, hch, v', u, hv', hu, hout⟩ |
      ⟨a, j, x, hhe, u, hu, hx⟩
    · exact absurd (.inl ⟨q', hq', a, j, x, hch, u, by rwa [hs] at hu, hx⟩) hc
    · by_cases hqq : q' = q
      · subst hqq
        rw [hgq] at hv'
        cases hv'
        exact ⟨a, j, x, hch, u, by rwa [hs] at hu, hout⟩
      · exact absurd (.inr (.inl ⟨q', a, j, x, hch, v', u, by rwa [hg _ _ hqq] at hv',
          by rwa [hs] at hu, hout⟩)) hc
    · exact absurd (.inr (.inr ⟨a, j, x, hhe, u, by rwa [hs] at hu, hx⟩)) hc
  · -- the hit has probability at most `δ`, and only if the next honest value is sampled
    rcases hch : T.chS q with _ | ⟨a, j, x⟩
    · rw [prEvent_eq_zero_of_forall_not _ _ fun v hv => by
        obtain ⟨a, j, x, h, -⟩ := hv; rw [hch] at h; cases h]
      exact zero_le
    · cases hu : c (.inr (a, T.ix (j + 1))) with
      | none =>
        rw [prEvent_eq_zero_of_forall_not _ _ fun v hv => by
          obtain ⟨a', j', x', h, u, hu', -⟩ := hv
          rw [hch] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [hu] at hu'; cases hu']
        exact zero_le
      | some u =>
        have hpi : propInd (∃ a' j' x', some (a, j, x) = some (a', j', x') ∧
            (c (.inr (a', T.ix (j' + 1)))).isSome) = 1 :=
          propInd_eq_one_iff.2 ⟨a, j, x, rfl, by rw [hu]; rfl⟩
        rw [hpi, mul_one]
        refine (prEvent_mono _ _ _ fun v hv => ?_).trans (hδ (T.out u))
        obtain ⟨a', j', x', h, u', hu', hout⟩ := hv
        rw [hch] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [hu] at hu'; cases hu'
        exact hout
  · -- the new pending charge
    intro v
    unfold Pot
    have h1 : (fl.countP fun q' => decide (T.pGF (c.cacheQuery (.inl q) v) q')) =
        fl.countP fun q' => decide (T.pGF c q') := by
      congr 1
    have h3 : T.pHE he (c.cacheQuery (.inl q) v) ↔ T.pHE he c := by simp only [pHE, hs]
    have h2 : ((Finset.univ.filter fun q' => T.pHit (c.cacheQuery (.inl q) v) q').card : ℕ) ≤
        (Finset.univ.filter fun q' => T.pHit c q').card + (if Nx then 1 else 0) := by
      have hsub : (Finset.univ.filter fun q' => T.pHit (c.cacheQuery (.inl q) v) q') ⊆
          (if Nx then insert q else id) (Finset.univ.filter fun q' => T.pHit c q') := by
        intro q' hq'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq'
        by_cases hqq : q' = q
        · subst hqq
          have hN : Nx := by
            obtain ⟨a, j, x, hch, -, hn⟩ := hq'
            exact ⟨a, j, x, hch, by rwa [hs] at hn⟩
          simp [hN]
        · have : T.pHit c q' := by
            obtain ⟨a, j, x, hch, hsome, hn⟩ := hq'
            exact ⟨a, j, x, hch, by rwa [hg _ _ hqq] at hsome, by rwa [hs] at hn⟩
          split_ifs <;> simp [this]
      refine (Finset.card_le_card hsub).trans ?_
      split_ifs
      · exact Finset.card_insert_le _ _
      · simp
    rw [h1, propInd_congr h3]
    have h2' : (((Finset.univ.filter fun q' => T.pHit (c.cacheQuery (.inl q) v) q').card : ℕ) :
        ℝ≥0∞) ≤ ((Finset.univ.filter fun q' => T.pHit c q').card : ℕ) + propInd Nx := by
      have := Nat.cast_le (α := ℝ≥0∞).2 h2
      push_cast at this
      refine this.trans (le_of_eq ?_)
      by_cases hN : Nx <;> simp [hN, propInd]
    calc _ ≤ δ * (fl.countP fun q' => decide (T.pGF c q')) +
          δ * (((Finset.univ.filter fun q' => T.pHit c q').card : ℕ) + propInd Nx) +
            δ * propInd (T.pHE he c) + κ * (fl.countP fun q' => decide (T.isKey q')) := by
          gcongr
      _ = _ := by ring
  · -- `D + Ψ' ≤ Pot + charge`
    rw [← add_assoc, add_comm _ (T.Pot δ κ fl he c), add_assoc]
    refine add_le_add le_rfl ?_
    rcases hch : T.chS q with _ | ⟨a, j, x⟩
    · simp [hNx, hch, propInd]
    · cases hu : c (.inr (a, T.ix (j + 1))) with
      | none =>
        have : Nx := ⟨a, j, x, hch, hu⟩
        simp [this, propInd, hu]
      | some u =>
        have : ¬ Nx := by
          rintro ⟨a', j', x', h, hn⟩
          rw [hch] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [hu] at hn; cases hn
        simp [this, propInd, hu]

/-- A fresh honest value: it fires exactly the pending candidates at its index, each with
probability at most `δ`, and removes them from the pending charge. -/
theorem fresh_s (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y)) (c : T.C2) (i : T.HIdx)
    (hi : c (.inr i) = none) (hc : ¬ T.Hz fl he c) :
    ex ($ᵗ St : ProbComp St) (fun u => hz (T.Hz fl he) (T.Pot δ κ fl he)
        (c.cacheQuery (.inr i) u)) ≤ T.Pot δ κ fl he c := by
  have hsi : ∀ u, (c.cacheQuery (.inr i) u) (.inr i) = some u := fun u =>
    QueryCache.cacheQuery_self _ _ _
  have hs : ∀ u i', i' ≠ i → (c.cacheQuery (.inr i) u) (.inr i') = c (.inr i') := fun u i' h =>
    QueryCache.cacheQuery_of_ne _ _ (by simpa using h)
  have hg : ∀ u q, (c.cacheQuery (.inr i) u) (.inl q) = c (.inl q) := fun u q =>
    QueryCache.cacheQuery_of_ne _ _ (by simp)
  -- candidates at the index `i`
  set aGF : St × Blk → Prop := fun q => ∃ a j x, T.chS q = some (a, j, x) ∧ (a, T.ix j) = i
  set aHit : St × Blk → Prop := fun q => ∃ a j x, T.chS q = some (a, j, x) ∧
    (a, T.ix (j + 1)) = i ∧ (c (.inl q)).isSome
  set aHE : Prop := ∃ a j x, he = some (a, j, x) ∧ (a, T.ix j) = i
  set Fu : St → Prop := fun u =>
    (∃ q ∈ fl, ∃ a j x, T.chS q = some (a, j, x) ∧ (a, T.ix j) = i ∧ T.out u = x) ∨
    (∃ q, ∃ a j x, T.chS q = some (a, j, x) ∧ (a, T.ix (j + 1)) = i ∧
      ∃ v, c (.inl q) = some v ∧ T.out u = T.out v) ∨
    (∃ a j x, he = some (a, j, x) ∧ (a, T.ix j) = i ∧ T.out u = x)
  -- the pending predicates after the sample
  have hpGF : ∀ u q, T.pGF (c.cacheQuery (.inr i) u) q ↔ T.pGF c q ∧ ¬ aGF q := by
    intro u q
    constructor
    · rintro ⟨a, j, x, hch, hn⟩
      by_cases he' : (a, T.ix j) = i
      · rw [he', hsi] at hn; cases hn
      · refine ⟨⟨a, j, x, hch, by rwa [hs _ _ he'] at hn⟩, ?_⟩
        rintro ⟨a', j', x', hch', he''⟩
        rw [hch] at hch'
        simp only [Option.some.injEq, Prod.mk.injEq] at hch'
        obtain ⟨rfl, rfl, rfl⟩ := hch'
        exact he' he''
    · rintro ⟨⟨a, j, x, hch, hn⟩, hna⟩
      have he' : (a, T.ix j) ≠ i := fun h => hna ⟨a, j, x, hch, h⟩
      exact ⟨a, j, x, hch, by rwa [hs _ _ he']⟩
  have hpHit : ∀ u q, T.pHit (c.cacheQuery (.inr i) u) q ↔ T.pHit c q ∧ ¬ aHit q := by
    intro u q
    constructor
    · rintro ⟨a, j, x, hch, hsome, hn⟩
      rw [hg] at hsome
      by_cases he' : (a, T.ix (j + 1)) = i
      · rw [he', hsi] at hn; cases hn
      · refine ⟨⟨a, j, x, hch, hsome, by rwa [hs _ _ he'] at hn⟩, ?_⟩
        rintro ⟨a', j', x', hch', he'', -⟩
        rw [hch] at hch'
        simp only [Option.some.injEq, Prod.mk.injEq] at hch'
        obtain ⟨rfl, rfl, rfl⟩ := hch'
        exact he' he''
    · rintro ⟨⟨a, j, x, hch, hsome, hn⟩, hna⟩
      have he' : (a, T.ix (j + 1)) ≠ i := fun h => hna ⟨a, j, x, hch, h, hsome⟩
      exact ⟨a, j, x, hch, by rwa [hg], by rwa [hs _ _ he']⟩
  have hpHE : ∀ u, T.pHE he (c.cacheQuery (.inr i) u) ↔ T.pHE he c ∧ ¬ aHE := by
    intro u
    constructor
    · rintro ⟨a, j, x, hhe, hn⟩
      by_cases he' : (a, T.ix j) = i
      · rw [he', hsi] at hn; cases hn
      · refine ⟨⟨a, j, x, hhe, by rwa [hs _ _ he'] at hn⟩, ?_⟩
        rintro ⟨a', j', x', hhe', he''⟩
        rw [hhe] at hhe'
        simp only [Option.some.injEq, Prod.mk.injEq] at hhe'
        obtain ⟨rfl, rfl, rfl⟩ := hhe'
        exact he' he''
    · rintro ⟨⟨a, j, x, hhe, hn⟩, hna⟩
      have he' : (a, T.ix j) ≠ i := fun h => hna ⟨a, j, x, hhe, h⟩
      exact ⟨a, j, x, hhe, by rwa [hs _ _ he']⟩
  -- the candidates at `i` are pending before the sample
  have haGF : ∀ q, aGF q → T.pGF c q := by
    rintro q ⟨a, j, x, hch, he'⟩; exact ⟨a, j, x, hch, by rw [he']; exact hi⟩
  have haHit : ∀ q, aHit q → T.pHit c q := by
    rintro q ⟨a, j, x, hch, he', hsome⟩; exact ⟨a, j, x, hch, hsome, by rw [he']; exact hi⟩
  have haHE : aHE → T.pHE he c := by
    rintro ⟨a, j, x, hhe, he'⟩; exact ⟨a, j, x, hhe, by rw [he']; exact hi⟩
  set Ψ' : ℝ≥0∞ := δ * (fl.countP fun q => decide (T.pGF c q ∧ ¬ aGF q)) +
    δ * ((Finset.univ.filter fun q => T.pHit c q ∧ ¬ aHit q).card : ℕ) +
      δ * propInd (T.pHE he c ∧ ¬ aHE) + κ * (fl.countP fun q => decide (T.isKey q)) with hΨ'
  set D : ℝ≥0∞ := δ * (fl.countP fun q => decide (aGF q)) +
    (δ * ((Finset.univ.filter fun q => aHit q).card : ℕ) + δ * propInd aHE) with hD
  refine (ex_hz_fresh_le _ _ _ _ Fu D Ψ' ?_ ?_ ?_).trans (le_of_eq ?_)
  · -- a new hazard is a candidate at `i`
    intro u hu
    rcases hu with ⟨q, hq, a, j, x, hch, u', hu', hx⟩ | ⟨q, a, j, x, hch, v, u', hv, hu', hout⟩ |
      ⟨a, j, x, hhe, u', hu', hx⟩
    · by_cases he' : (a, T.ix j) = i
      · rw [he', hsi] at hu'; cases hu'
        exact .inl ⟨q, hq, a, j, x, hch, he', hx.symm⟩
      · exact absurd (.inl ⟨q, hq, a, j, x, hch, u', by rwa [hs _ _ he'] at hu', hx⟩) hc
    · rw [hg] at hv
      by_cases he' : (a, T.ix (j + 1)) = i
      · rw [he', hsi] at hu'; cases hu'
        exact .inr (.inl ⟨q, a, j, x, hch, he', v, hv, hout.symm⟩)
      · exact absurd (.inr (.inl ⟨q, a, j, x, hch, v, u', hv, by rwa [hs _ _ he'] at hu',
          hout⟩)) hc
    · by_cases he' : (a, T.ix j) = i
      · rw [he', hsi] at hu'; cases hu'
        exact .inr (.inr ⟨a, j, x, hhe, he', hx.symm⟩)
      · exact absurd (.inr (.inr ⟨a, j, x, hhe, u', by rwa [hs _ _ he'] at hu', hx⟩)) hc
  · -- union bound
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ((prEvent_or_le _ _ _).trans
      (add_le_add ?_ ?_)))
    · refine prEvent_exists_list_le_countP _ fl (fun q u => ∃ a j x, T.chS q = some (a, j, x) ∧
        (a, T.ix j) = i ∧ T.out u = x) aGF δ fun q => ?_
      rcases hch : T.chS q with _ | ⟨a, j, x⟩
      · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => by
          obtain ⟨a, j, x, h, -⟩ := hu; (try rw [hch] at h); cases h]
        exact zero_le
      · by_cases he' : (a, T.ix j) = i
        · rw [propInd_eq_one_iff.2 ⟨a, j, x, hch, he'⟩, mul_one]
          refine (prEvent_mono _ _ _ fun u hu => ?_).trans (hδ x)
          obtain ⟨a', j', x', h, -, hx⟩ := hu
          try rw [hch] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact hx
        · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => by
            obtain ⟨a', j', x', h, he'', -⟩ := hu
            try rw [hch] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact he' he'']
          exact zero_le
    · refine prEvent_exists_fintype_le _ (fun q u => ∃ a j x, T.chS q = some (a, j, x) ∧
        (a, T.ix (j + 1)) = i ∧ ∃ v, c (.inl q) = some v ∧ T.out u = T.out v) aHit δ fun q => ?_
      rcases hch : T.chS q with _ | ⟨a, j, x⟩
      · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => by
          obtain ⟨a, j, x, h, -⟩ := hu; (try rw [hch] at h); cases h]
        exact zero_le
      · cases hv : c (.inl q) with
        | none =>
          rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => by
            obtain ⟨a', j', x', -, -, v, hv', -⟩ := hu
            (try rw [hv] at hv'); cases hv']
          exact zero_le
        | some v =>
          by_cases he' : (a, T.ix (j + 1)) = i
          · rw [propInd_eq_one_iff.2 ⟨a, j, x, hch, he', by rw [hv]; rfl⟩, mul_one]
            refine (prEvent_mono _ _ _ fun u hu => ?_).trans (hδ (T.out v))
            obtain ⟨a', j', x', -, -, v', hv', hout⟩ := hu
            (try rw [hv] at hv'); cases hv'
            exact hout
          · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => by
              obtain ⟨a', j', x', h, he'', -⟩ := hu
              try rw [hch] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact he' he'']
            exact zero_le
    · by_cases ha : aHE
      · obtain ⟨a, j, x, hhe, he'⟩ := ha
        rw [propInd_eq_one_iff.2 ⟨a, j, x, hhe, he'⟩, mul_one]
        refine (prEvent_mono _ _ _ fun u hu => ?_).trans (hδ x)
        obtain ⟨a', j', x', h, -, hx⟩ := hu
        rw [hhe] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact hx
      · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => by
          obtain ⟨a', j', x', h, he'', -⟩ := hu
          exact ha ⟨a', j', x', h, he''⟩]
        exact zero_le
  · -- the pending charge after the sample
    intro u
    unfold Pot
    have h1 : (fl.countP fun q => decide (T.pGF (c.cacheQuery (.inr i) u) q)) =
        fl.countP fun q => decide (T.pGF c q ∧ ¬ aGF q) := by
      congr 1; funext q; exact decide_eq_decide.2 (hpGF u q)
    have h2 : (Finset.univ.filter fun q => T.pHit (c.cacheQuery (.inr i) u) q) =
        Finset.univ.filter fun q => T.pHit c q ∧ ¬ aHit q := by
      ext q; simp [hpHit u q]
    rw [h1, h2, propInd_congr (hpHE u)]
  · -- `D + Ψ' = Pot`
    unfold Pot
    rw [countP_split fl (T.pGF c) (fun q => T.pGF c q ∧ ¬ aGF q) aGF
        (fun q => ⟨fun h => (Classical.em (aGF q)).elim .inr fun h' => .inl ⟨h, h'⟩,
          fun h => h.elim And.left (haGF q)⟩) (fun q h => h.1.2 h.2),
      card_split (T.pHit c) (fun q => T.pHit c q ∧ ¬ aHit q) aHit
        (fun q => ⟨fun h => (Classical.em (aHit q)).elim .inr fun h' => .inl ⟨h, h'⟩,
          fun h => h.elim And.left (haHit q)⟩) (fun q h => h.1.2 h.2)]
    have h3 : propInd (T.pHE he c) = propInd (T.pHE he c ∧ ¬ aHE) + propInd aHE := by
      by_cases ha : aHE
      · simp [propInd, ha, haHE ha]
      · simp [propInd, ha]
    rw [h3, hD, hΨ']
    push_cast
    ring

/-- The lazy tables' handler at the `.inl`/`.inr` split. -/
theorem romImpl_run_inl (n : ℕ) (c : T.C2) :
    ((T.spec2).romImpl (.inl n)).run c =
      (fun u => (u, c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) :=
  roSim.run_apply_inl _ n c

/-- **One lazy-table step.** -/
theorem rom_step (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y))
    (t : ℕ ⊕ ((St × Blk) ⊕ T.HIdx)) (c : T.C2) (hc : ¬ T.Hz fl he c) :
    ex (((T.spec2).romImpl t).run c) (fun z => hz (T.Hz fl he) (T.Pot δ κ fl he) z.2) ≤
      T.Pot δ κ fl he c + (if T.isHSF t = true then δ else 0) := by
  rcases t with n | t
  · rw [romImpl_run_inl, ex_map]
    simp only [Function.comp_def, ex_const, hz_of_not_P hc]
    exact le_self_add
  · rw [romImpl_apply_inr, randomOracle.run_eq]
    cases h : c t with
    | some v =>
      simp only [ex_pure, hz_of_not_P hc]
      exact le_self_add
    | none =>
      simp only [ex_bind, ex_pure]
      rcases t with q | i
      · exact T.fresh_g κ hδ fl he c q h hc
      · exact (T.fresh_s κ hδ fl he c i h hc).trans le_self_add

/-- Cached values persist along a lazy-table run. -/
theorem cache_persist {α : Type} (X : OracleComp (unifSpec + T.spec2) α) (c : T.C2)
    (t : (St × Blk) ⊕ T.HIdx) (v : T.spec2.Range t) (hv : c t = some v) :
    ∀ z ∈ support ((simulateQ (T.spec2).romImpl X).run c), z.2 t = some v := by
  refine simulateQ_run_preservesInv _ (fun c : T.C2 => c t = some v) ?_ X c hv
  rintro (n | t') s hs z hz
  · rw [romImpl_run_inl, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · rw [romImpl_apply_inr, randomOracle.run_eq] at hz
    cases h : s t' with
    | none =>
      rw [h] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      by_cases ht : t = t'
      · subst ht; rw [hs] at h; cases h
      · exact (QueryCache.cacheQuery_of_ne _ _ ht).trans hs
    | some u =>
      rw [h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hs

theorem Hz_mono (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y)) {c c' : T.C2}
    (hcc : ∀ t (v : T.spec2.Range t), c t = some v → c' t = some v) (h : T.Hz fl he c) :
    T.Hz fl he c' := by
  rcases h with ⟨q, hq, a, j, x, hch, u, hu, hx⟩ | ⟨q, a, j, x, hch, v, u, hv, hu, hout⟩ |
    ⟨a, j, x, hhe, u, hu, hx⟩
  · exact .inl ⟨q, hq, a, j, x, hch, u, hcc _ _ hu, hx⟩
  · exact .inr (.inl ⟨q, a, j, x, hch, v, u, hcc _ _ hv, hcc _ _ hu, hout⟩)
  · exact .inr (.inr ⟨a, j, x, hhe, u, hcc _ _ hu, hx⟩)

/-- **A whole lazy-table program**: with at most `n` fresh-`g0`-chain-cell queries, the expected
`hz` rises by at most `n δ`. -/
theorem rom_run_le (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (fl : List (St × Blk)) (he : Option (Fin T.m × ℕ × Y)) {α : Type}
    (X : OracleComp (unifSpec + T.spec2) α) (n : ℕ)
    (hn : IsQueryBoundP X (fun t => T.isHSF t = true) n) (c : T.C2) :
    ex ((simulateQ (T.spec2).romImpl X).run c) (fun z => hz (T.Hz fl he) (T.Pot δ κ fl he) z.2) ≤
      hz (T.Hz fl he) (T.Pot δ κ fl he) c + n * δ := by
  refine ex_hz_le_of_step _ (fun _ => True) (T.Hz fl he) (T.Pot δ κ fl he) _ δ
    (fun _ _ _ _ _ => trivial) (fun t s _ hs z hz => ?_) (fun t s _ hs => T.rom_step κ hδ fl he t s hs)
    X n hn c trivial
  refine T.Hz_mono fl he (fun t' v hv => ?_) hs
  have := T.cache_persist (liftM ((unifSpec + T.spec2).query t)) s t' v hv z
  simp only [simulateQ_spec_query] at this
  exact this hz

end Params

end Ideal.Direct.Toy

#print axioms Ideal.Direct.Toy.Params.fresh_g
#print axioms Ideal.Direct.Toy.Params.fresh_s
#print axioms Ideal.Direct.Toy.Params.rom_run_le
