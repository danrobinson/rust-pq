import Ideal.Direct.ToyRom

/-!
# The toy game: the bound on the deferred game, and the headline `toy_le`

* Support facts for the deferred routing (`rom_query_supp`, `core_supp`): a routing step samples
  honest values only at revealed positions, and reads `g0` only at its own cell.
* Query counts (`qb_core`, `qb_walkX`, `qb_compS`): a routing step makes at most one charged
  lazy-table query (a fresh `g0` chain cell), and only if its cell is a chain cell.
* `comb`: the deferred handler fused with the lazy tables; `comb_step`: one adversary step
  raises the expected `hz` by at most `max (2δ) κ` if it is a compression query (a chain
  query: `δ` now or pending for the hit, `δ` pending for the guess; a secret-keyed query: `κ`
  pending until the secret is drawn) and by nothing otherwise (a reveal or a coin).
* `G2_le`: the deferred game's event has probability at most `q · max (2δ) κ + (w + 1) δ`.
* **`toy_le`**: the same bound for the real game.
-/

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Toy

namespace Params

open Classical

variable {St Blk K Y : Type} (T : Params St Blk K Y)
variable [DecidableEq St] [DecidableEq Blk] [DecidableEq Y] [Fintype St] [Fintype Blk]
  [SampleableType St] [DecidableEq K] [Fintype K] [SampleableType K]

/-! ## Support facts -/

theorem rom_query_supp (t : (St × Blk) ⊕ T.HIdx) (c : T.C2) (z : T.spec2.Range t × T.C2)
    (hz : z ∈ support ((simulateQ (T.spec2).romImpl
      (liftM ((unifSpec + T.spec2).query (.inr t)) :
        OracleComp (unifSpec + T.spec2) (T.spec2.Range t))).run c)) :
    z.2 t = some z.1 ∧ ∀ t', t' ≠ t → z.2 t' = c t' := by
  simp only [simulateQ_spec_query, romImpl_apply_inr, randomOracle.run_eq] at hz
  cases h : c t with
  | some v =>
    rw [h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨h, fun _ _ => rfl⟩
  | none =>
    rw [h] at hz
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨QueryCache.cacheQuery_self _ _ _, fun t' ht' => QueryCache.cacheQuery_of_ne _ _ ht'⟩

theorem revPos_eq_some {r : Fin T.m → ℕ} {q : St × Blk} {a : Fin T.m} {j : ℕ} {x : Y} :
    T.revPos r q = some (a, j, x) ↔ T.chS q = some (a, j, x) ∧ r a ≤ j := by
  rw [chS_eq_some]
  unfold revPos
  by_cases hc : q.1 = T.cv
  · simp only [hc, if_true, true_and]
    rcases T.parse q.2 with ⟨a', k'⟩ | ⟨a', j', x'⟩ | _
    · simp
    · by_cases hj : j' < T.w ∧ r a' ≤ j'
      · simp only [hj, and_self, if_true, Option.some.injEq, Prod.mk.injEq, Shape.chn.injEq]
        constructor
        · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨⟨rfl, rfl, rfl⟩, hj.1⟩, hj.2⟩
        · rintro ⟨⟨⟨rfl, rfl, rfl⟩, -⟩, -⟩; exact ⟨rfl, rfl, rfl⟩
      · simp only [hj, if_false]
        constructor
        · intro h; cases h
        · rintro ⟨⟨⟨rfl, rfl, rfl⟩, h1⟩, h2⟩; exact absurd ⟨h1, h2⟩ hj
    · simp
  · simp [hc]

/-- Support of one routing step. -/
theorem core_supp (r : Fin T.m → ℕ) (q : St × Blk) (c : T.C2) (z : (St × Bool) × T.C2)
    (hz : z ∈ support ((simulateQ (T.spec2).romImpl (T.core r q)).run c)) :
    (z.1.2 = true → z.2 (.inl q) = some z.1.1) ∧
    (∀ q', q' ≠ q → z.2 (.inl q') = c (.inl q')) ∧
    (∀ i, z.2 (.inr i) ≠ c (.inr i) → ∃ a j x, T.revPos r q = some (a, j, x) ∧
      (i = (a, T.ix j) ∨ i = (a, T.ix (j + 1)))) ∧
    (z.1.2 = true → ∀ a j x, T.revPos r q = some (a, j, x) →
      ∃ u, z.2 (.inr (a, T.ix j)) = some u ∧ T.out u ≠ x) := by
  unfold core at hz
  rcases hrp : T.revPos r q with _ | ⟨a, j, x⟩
  · rw [hrp] at hz
    simp only [simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := T.rom_query_supp (.inl q) c y hy
    refine ⟨fun _ => h1, fun q' hq' => h2 _ (by simpa using hq'), fun i hi => ?_, ?_⟩
    · exact absurd (h2 _ (by simp)) hi
    · intro _ a j x h; cases h
  · rw [hrp] at hz
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨h1, h2⟩ := T.rom_query_supp (.inr (a, T.ix j)) c y hy
    by_cases hx : T.out y.1 = x
    · simp only [hx, if_true, simulateQ_map, StateT.run_map, support_map] at hz
      obtain ⟨y', hy', rfl⟩ := hz
      obtain ⟨h1', h2'⟩ := T.rom_query_supp (.inr (a, T.ix (j + 1))) y.2 y' hy'
      refine ⟨fun h => (by simp at h), fun (q' : St × Blk) _ => (h2' _ (by simp)).trans
        (h2 _ (by simp)), fun i hi => ?_, fun h => (by simp at h)⟩
      by_cases e1 : i = (a, T.ix j)
      · exact ⟨a, j, x, rfl, .inl e1⟩
      · by_cases e2 : i = (a, T.ix (j + 1))
        · exact ⟨a, j, x, rfl, .inr e2⟩
        · exact absurd ((h2' _ (by simpa using e2)).trans (h2 _ (by simpa using e1))) hi
    · simp only [hx, if_false, simulateQ_map, StateT.run_map, support_map] at hz
      obtain ⟨y', hy', rfl⟩ := hz
      obtain ⟨h1', h2'⟩ := T.rom_query_supp (.inl q) y.2 y' hy'
      refine ⟨fun _ => h1', fun q' hq' => (h2' _ (by simpa using hq')).trans (h2 _ (by simp)),
        fun i hi => ?_, fun _ a' j' x' h => ?_⟩
      · by_cases e1 : i = (a, T.ix j)
        · exact ⟨a, j, x, rfl, .inl e1⟩
        · exact absurd ((h2' _ (by simp)).trans (h2 _ (by simpa using e1))) hi
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨y.1, (h2' _ (by simp)).trans h1, hx⟩

/-- Honest values are sampled only at revealed positions. -/
def Inv1 (r : Fin T.m → ℕ) (c : T.C2) : Prop :=
  ∀ a (j : Fin (T.w + 1)), (c (.inr (a, j))).isSome → r a ≤ j

theorem ix_val_of_lt {j : ℕ} (hj : j < T.w) : (T.ix j).val = j ∧ (T.ix (j + 1)).val = j + 1 :=
  ⟨T.ix_val (by omega), T.ix_val (by omega)⟩

theorem core_Inv1 (r : Fin T.m → ℕ) (q : St × Blk) (c : T.C2) (hc : T.Inv1 r c)
    (z : (St × Bool) × T.C2) (hz : z ∈ support ((simulateQ (T.spec2).romImpl (T.core r q)).run c)) :
    T.Inv1 r z.2 := by
  obtain ⟨-, -, h3, -⟩ := T.core_supp r q c z hz
  intro a' j' hs
  by_cases hch : z.2 (.inr (a', j')) = c (.inr (a', j'))
  · exact hc a' j' (by rwa [← hch])
  · obtain ⟨a, j, x, hrp, he⟩ := h3 _ hch
    obtain ⟨hch', hr⟩ := T.revPos_eq_some.1 hrp
    have hj : j < T.w := ((T.chS_eq_some).1 hch').2.2
    obtain ⟨e1, e2⟩ := T.ix_val_of_lt hj
    rcases he with he | he <;> simp only [Prod.mk.injEq] at he <;> obtain ⟨rfl, rfl⟩ := he
    · rw [e1]; exact hr
    · rw [e2]; omega

/-- A logged query after a routing step fires no guess. -/
theorem core_noGF (r : Fin T.m → ℕ) (q : St × Blk) (c : T.C2) (hc : T.Inv1 r c)
    (z : (St × Bool) × T.C2) (hz : z ∈ support ((simulateQ (T.spec2).romImpl (T.core r q)).run c))
    (hb : z.1.2 = true) : ¬ T.GFc z.2 q := by
  obtain ⟨-, -, h3, h4⟩ := T.core_supp r q c z hz
  rintro ⟨a, j, x, hch, u, hu, hx⟩
  have hj : j < T.w := ((T.chS_eq_some).1 hch).2.2
  by_cases hr : r a ≤ j
  · obtain ⟨u', hu', hne⟩ := h4 hb a j x (T.revPos_eq_some.2 ⟨hch, hr⟩)
    rw [hu] at hu'; cases hu'
    exact hne hx.symm
  · by_cases hch2 : z.2 (.inr (a, T.ix j)) = c (.inr (a, T.ix j))
    · have := hc a (T.ix j) (by rw [← hch2, hu]; rfl)
      rw [(T.ix_val_of_lt hj).1] at this
      exact hr this
    · obtain ⟨a', j', x', hrp, -⟩ := h3 _ hch2
      obtain ⟨hch', hr'⟩ := T.revPos_eq_some.1 hrp
      rw [hch] at hch'
      simp only [Option.some.injEq, Prod.mk.injEq] at hch'
      obtain ⟨rfl, rfl, rfl⟩ := hch'
      exact hr hr'

/-! ## Query counts -/

theorem qb_qG (q : St × Blk) :
    IsQueryBoundP (T.qG q) (fun t => T.isHSF t = true) (if (T.chS q).isSome then 1 else 0) := by
  rw [isQueryBoundP_query_iff]
  intro h
  simp only [isHSF] at h
  simp [h]

theorem qb_qS (i : T.HIdx) : IsQueryBoundP (T.qS i) (fun t => T.isHSF t = true) 0 := by
  rw [isQueryBoundP_query_iff]
  intro h; simp [isHSF] at h

theorem qb_core (r : Fin T.m → ℕ) (q : St × Blk) :
    IsQueryBoundP (T.core r q) (fun t => T.isHSF t = true)
      (if (T.chS q).isSome then 1 else 0) := by
  unfold core
  rcases T.revPos r q with _ | ⟨a, j, x⟩
  · exact (isQueryBoundP_map_iff _ _ _).2 (T.qb_qG q)
  · have := isQueryBoundP_bind (T.qb_qS (a, T.ix j)) (m := if (T.chS q).isSome then 1 else 0)
      (ob := fun u => if T.out u = x then (fun u' => (u', false)) <$> T.qS (a, T.ix (j + 1))
        else (fun v => (v, true)) <$> T.qG q) fun u _ => by
        split
        · exact ((isQueryBoundP_map_iff _ _ _).2 (T.qb_qS _)).mono (Nat.zero_le _)
        · exact (isQueryBoundP_map_iff _ _ _).2 (T.qb_qG q)
    simpa using this

theorem qb_core_le (r : Fin T.m → ℕ) (q : St × Blk) :
    IsQueryBoundP (T.core r q) (fun t => T.isHSF t = true) 1 :=
  (T.qb_core r q).mono (by split_ifs <;> omega)

theorem qb_walkX (r : Fin T.m → ℕ) (a : Fin T.m) (n : ℕ) :
    ∀ j x, IsQueryBoundP (T.walkX r a j n x) (fun t => T.isHSF t = true) n := by
  induction n with
  | zero => intro j x; exact isQueryBoundP_pure _ _ _
  | succ n ih =>
    intro j x
    rw [walkX]
    have h := isQueryBoundP_bind (T.qb_core_le r (T.cv, T.F a j x)) fun vb _ =>
      isQueryBoundP_bind (ih (j + 1) (T.out vb.1)) fun z _ => isQueryBoundP_pure
        (fun t => T.isHSF t = true)
        (z.1, if vb.2 then ((T.cv, T.F a j x), vb.1) :: z.2 else z.2) 0
    rwa [add_zero, Nat.add_comm 1 n] at h

theorem qb_compS : IsQueryBoundP T.compS (fun t => T.isHSF t = true) 0 := by
  have : ∀ (l : List T.HIdx) (f : T.HIdx → St), IsQueryBoundP
      (l.foldlM (fun f i => (fun u => Function.update f i u) <$> T.qS i) f)
      (fun t => T.isHSF t = true) 0 := by
    intro l
    induction l with
    | nil => intro f; exact isQueryBoundP_pure _ _ _
    | cons i l ih =>
      intro f
      rw [List.foldlM_cons]
      exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_map_iff _ _ _).2 (T.qb_qS i)) ih
  exact this _ _

/-! ## Support of the walk and of the completion -/

theorem walk_supp (r : Fin T.m → ℕ) (a : Fin T.m) (n : ℕ) :
    ∀ j x (c : T.C2), T.Inv1 r c →
      ∀ z ∈ support ((simulateQ (T.spec2).romImpl (T.walkX r a j n x)).run c),
        T.Inv1 r z.2 ∧ ∀ e ∈ z.1.2, z.2 (.inl e.1) = some e.2 := by
  induction n with
  | zero =>
    intro j x c hc z hz
    simp only [walkX, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hc, by simp⟩
  | succ n ih =>
    intro j x c hc z hz
    simp only [walkX, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, y', hy', rfl⟩ := hz
    have hc1 := T.core_Inv1 r _ c hc y hy
    obtain ⟨hI', hlog⟩ := ih (j + 1) _ y.2 hc1 y' hy'
    refine ⟨hI', fun e he => ?_⟩
    by_cases hb : y.1.2 = true
    · simp only [hb, if_true, List.mem_cons] at he
      rcases he with rfl | he
      · exact T.cache_persist _ y.2 _ _ ((T.core_supp r _ c y hy).1 hb) y' hy'
      · exact hlog e he
    · simp only [hb] at he
      exact hlog e (by simpa using he)

theorem compS_supp (c : T.C2) :
    ∀ z ∈ support ((simulateQ (T.spec2).romImpl T.compS).run c), ∀ i, z.2 (.inr i) = some (z.1 i) := by
  have key : ∀ (l : List T.HIdx) (f : T.HIdx → St) (c : T.C2) (S : T.HIdx → Prop),
      (∀ i, S i → c (.inr i) = some (f i)) →
      ∀ z ∈ support ((simulateQ (T.spec2).romImpl
        (l.foldlM (fun f i => (fun u => Function.update f i u) <$> T.qS i) f)).run c),
        ∀ i, (S i ∨ i ∈ l) → z.2 (.inr i) = some (z.1 i) := by
    intro l
    induction l with
    | nil =>
      intro f c S hS z hz i hi
      simp only [List.foldlM_nil, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact hS i (hi.resolve_right (by simp))
    | cons i0 l ih =>
      intro f c S hS z hz i hi
      simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
        simulateQ_map, StateT.run_map, support_map] at hz
      obtain ⟨y, ⟨y0, hy0, rfl⟩, hz⟩ := hz
      obtain ⟨h1, h2⟩ := T.rom_query_supp (.inr i0) c y0 hy0
      refine ih _ y0.2 (fun i => S i ∨ i = i0) (fun i hi' => ?_) z hz i ?_
      · by_cases e : i = i0
        · subst e; simp [h1]
        · rw [h2 _ (by simpa using e), hS i (hi'.resolve_right e)]
          simp [Function.update_of_ne e]
      · rcases hi with hi | hi
        · exact .inl (.inl hi)
        · rcases List.mem_cons.mp hi with rfl | hi
          · exact .inl (.inr rfl)
          · exact .inr hi
  intro z hz i
  exact key _ _ c (fun _ => False) (fun _ h => h.elim) z hz i (.inr (by simp))

/-! ## The fused handler and phase A -/

variable {δ : ℝ≥0∞} (κ : ℝ≥0∞)

/-- Invariant of the fused state. -/
def IA (p : GS T.m St Blk × T.C2) : Prop :=
  (∀ a, p.1.r a ≤ T.w + 1) ∧ T.Inv1 p.1.r p.2 ∧ ∀ e ∈ p.1.hl, p.2 (.inl e.1) = some e.2

/-- The deferred handler fused with the lazy tables. -/
noncomputable def comb : QueryImpl T.advSpec (StateT (GS T.m St Blk × T.C2) ProbComp) := fun t =>
  StateT.mk fun p => (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ (T.spec2).romImpl ((T.H2 t).run p.1)).run p.2

theorem comb_run {α : Type} (oa : OracleComp T.advSpec α) (gs : GS T.m St Blk) (c : T.C2) :
    (simulateQ (T.spec2).romImpl ((simulateQ T.H2 oa).run gs)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ T.comb oa).run (gs, c) :=
  simulateQ_StateT_StateT_compose _ _ _ (fun t s c => by
    show _ = (fun r => ((r.1, r.2.1), r.2.2)) <$> ((fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (T.spec2).romImpl ((T.H2 t).run s)).run c)
    simp [Functor.map_map]) oa gs c

theorem comb_inl (n : ℕ) (p : GS T.m St Blk × T.C2) :
    (T.comb (.inl n)).run p = (fun u => (u, p)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [comb, H2, StateT.run_mk, simulateQ_map, StateT.run_map, simulateQ_spec_query,
    romImpl_run_inl, Functor.map_map]
  rfl

theorem comb_hash (q : St × Blk) (gs : GS T.m St Blk) (c : T.C2) :
    (T.comb (.inr (.inl q))).run (gs, c) = (fun z => (z.1.1, (T.logH gs q z.1, z.2))) <$>
      (simulateQ (T.spec2).romImpl (T.core gs.r q)).run c := by
  simp only [comb, H2, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]

theorem comb_rev (ab : Fin T.m × ℕ) (gs : GS T.m St Blk) (c : T.C2) :
    (T.comb (.inr (.inr ab))).run (gs, c) =
      (fun z => (T.out z.1, ({ gs with r := T.rUpd gs.r ab.1 ab.2 }, z.2))) <$>
        (simulateQ (T.spec2).romImpl (T.qS (ab.1, T.ix (T.cl ab.2)))).run c := by
  simp only [comb, H2, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]

theorem Hz_fl_mono {fl fl' : List (St × Blk)} (h : ∀ q ∈ fl, q ∈ fl') (he : Option (Fin T.m × ℕ × Y))
    (c : T.C2) (hz : T.Hz fl he c) : T.Hz fl' he c := by
  rcases hz with ⟨q, hq, h'⟩ | h' | h'
  · exact .inl ⟨q, h q hq, h'⟩
  · exact .inr (.inl h')
  · exact .inr (.inr h')

theorem chS_not_key {q : St × Blk} (h1 : (T.chS q).isSome) : ¬ T.isKey q := by
  rcases h : T.chS q with _ | ⟨a, j, x⟩
  · rw [h] at h1; cases h1
  · rintro ⟨-, a', k', hk⟩
    rw [((T.chS_eq_some).1 h).2.1] at hk
    cases hk

/-- Logging a routed query raises the expected `hz` by at most its pending charges. -/
theorem hz_logH (gs : GS T.m St Blk) (q : St × Blk) (vb : St × Bool) (c' : T.C2)
    (hno : vb.2 = true → ¬ T.GFc c' q) :
    hz (T.Hz (T.logH gs q vb).fl none) (T.Pot δ κ (T.logH gs q vb).fl none) c' ≤
      hz (T.Hz gs.fl none) (T.Pot δ κ gs.fl none) c' +
        (δ * propInd ((T.chS q).isSome) + κ * propInd (T.isKey q)) := by
  unfold logH
  split_ifs with hb
  · have hiff : T.Hz (q :: gs.fl) none c' ↔ T.Hz gs.fl none c' := by
      constructor
      · rintro (⟨q', hq', h'⟩ | h' | h')
        · rcases List.mem_cons.mp hq' with rfl | hq'
          · exact absurd h' (hno hb)
          · exact .inl ⟨q', hq', h'⟩
        · exact .inr (.inl h')
        · exact .inr (.inr h')
      · exact T.Hz_fl_mono (fun q' h => List.mem_cons_of_mem _ h) none c'
    by_cases hH : T.Hz gs.fl none c'
    · rw [hz_of_P hH, hz_of_P (hiff.2 hH)]; exact le_self_add
    · rw [hz_of_not_P hH, hz_of_not_P (fun h => hH (hiff.1 h))]
      unfold Pot
      simp only [List.countP_cons]
      have hp' : (if decide (T.pGF c' q) = true then (1 : ℝ≥0∞) else 0) ≤
          propInd ((T.chS q).isSome) := by
        by_cases h1 : T.pGF c' q
        · have h2 : (T.chS q).isSome = true := by
            obtain ⟨a, j, x, hch, -⟩ := h1; simp [hch]
          simp [h1, h2, propInd]
        · simp [h1]
      have hk' : (if decide (T.isKey q) = true then (1 : ℝ≥0∞) else 0) = propInd (T.isKey q) := by
        by_cases h : T.isKey q <;> simp [h, propInd]
      push_cast
      rw [hk']
      calc _ ≤ δ * ((gs.fl.countP fun q => decide (T.pGF c' q) : ℕ) + propInd ((T.chS q).isSome)) +
            δ * ((Finset.univ.filter fun q => T.pHit c' q).card : ℕ) + δ * propInd (T.pHE none c') +
            κ * ((gs.fl.countP fun q => decide (T.isKey q) : ℕ) + propInd (T.isKey q)) := by
            gcongr
        _ = _ := by ring
  · exact le_self_add

/-- **One step of the fused handler.** -/
theorem comb_step (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (t : T.advSpec.Domain) (p : GS T.m St Blk × T.C2) (hI : T.IA p)
    (hP : ¬ T.Hz p.1.fl none p.2) :
    ex ((T.comb t).run p) (fun z => hz (fun p => T.Hz p.1.fl none p.2)
        (fun p => T.Pot δ κ p.1.fl none p.2) z.2) ≤
      T.Pot δ κ p.1.fl none p.2 + (if T.isHash t = true then max (2 * δ) κ else 0) := by
  obtain ⟨gs, c⟩ := p
  rcases t with n | q | ab
  · simp only [comb, H2, StateT.run_mk, simulateQ_map, StateT.run_map, ex_map, Function.comp_def]
    refine (T.rom_run_le κ hδ gs.fl none _ 0 ?_ c).trans ?_
    · rw [isQueryBoundP_query_iff]; intro h; simp [isHSF] at h
    · simp [hz_of_not_P hP, isHash]
  · simp only [comb, H2, StateT.run_mk, simulateQ_map, StateT.run_map, ex_map, Function.comp_def]
    refine (ex_mono_of_support _ fun z hz => T.hz_logH κ gs q z.1 z.2
      (fun hb => T.core_noGF gs.r q c hI.2.1 z hz hb)).trans ?_
    rw [ex_add, ex_const]
    refine (add_le_add (T.rom_run_le κ hδ gs.fl none _ _ (T.qb_core gs.r q) c) le_rfl).trans ?_
    rw [hz_of_not_P hP, add_assoc]
    refine add_le_add le_rfl ?_
    simp only [isHash, if_true]
    have hk1 : propInd (T.isKey q) ≤ 1 := by unfold propInd; split_ifs <;> simp
    by_cases h1 : (T.chS q).isSome
    · have h2 := T.chS_not_key h1
      rw [propInd_eq_one_iff.2 h1, propInd_eq_zero_iff.2 h2]
      simp only [h1, if_true, mul_zero, add_zero, Nat.cast_one, one_mul, mul_one]
      rw [← two_mul]; exact le_max_left _ _
    · rw [propInd_eq_zero_iff.2 h1]
      simp only [h1, Bool.false_eq_true, if_false, CharP.cast_eq_zero, zero_mul, zero_add,
        mul_zero]
      exact (mul_le_of_le_one_right' hk1).trans (le_max_right _ _)
  · simp only [comb, H2, StateT.run_mk, simulateQ_map, StateT.run_map, ex_map, Function.comp_def]
    refine (T.rom_run_le κ hδ gs.fl none _ 0 (T.qb_qS _) c).trans ?_
    simp [hz_of_not_P hP, isHash]

theorem comb_IA (t : T.advSpec.Domain) (p : GS T.m St Blk × T.C2) (hI : T.IA p) :
    ∀ z ∈ support ((T.comb t).run p), T.IA z.2 := by
  obtain ⟨gs, c⟩ := p
  obtain ⟨h0, h1, h3⟩ := hI
  intro z hz
  rcases t with n | q | ab
  · rw [comb_inl, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨h0, h1, h3⟩
  · rw [comb_hash, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨s1, -, -, -⟩ := T.core_supp gs.r q c y hy
    refine ⟨by simpa [logH_r] using h0, by simpa [logH_r] using T.core_Inv1 gs.r q c h1 y hy,
      fun e he => ?_⟩
    simp only at he ⊢
    unfold logH at he
    split_ifs at he with hb
    · rcases List.mem_cons.mp he with rfl | he
      · exact s1 hb
      · exact T.cache_persist _ c _ _ (h3 e he) y hy
    · exact T.cache_persist _ c _ _ (h3 e he) y hy
  · rw [comb_rev, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y1, y2⟩ := T.rom_query_supp (.inr (ab.1, T.ix (T.cl ab.2))) c y hy
    refine ⟨fun a => ?_, fun a' j' hs => ?_, fun e he => ?_⟩
    · show T.rUpd gs.r ab.1 ab.2 a ≤ T.w + 1
      unfold rUpd
      by_cases e : a = ab.1
      · subst e; rw [Function.update_self]; exact (min_le_left _ _).trans (h0 _)
      · rw [Function.update_of_ne e]; exact h0 a
    · show T.rUpd gs.r ab.1 ab.2 a' ≤ j'
      unfold rUpd
      by_cases e : (a', j') = (ab.1, T.ix (T.cl ab.2))
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [Function.update_self, T.ix_val (by simp [cl])]
        exact min_le_right _ _
      · have hne : (Sum.inr (a', j') : (St × Blk) ⊕ T.HIdx) ≠ Sum.inr (ab.1, T.ix (T.cl ab.2)) :=
          fun h => e (Sum.inr.inj h)
        have := h1 a' j' (by rw [← y2 _ hne]; exact hs)
        by_cases ea : a' = ab.1
        · subst ea; rw [Function.update_self]; exact (min_le_left _ _).trans this
        · rw [Function.update_of_ne ea]; exact this
    · exact (y2 _ (by simp)).trans (h3 e he)

theorem comb_abs (t : T.advSpec.Domain) (p : GS T.m St Blk × T.C2) (hP : T.Hz p.1.fl none p.2) :
    ∀ z ∈ support ((T.comb t).run p), T.Hz z.2.1.fl none z.2.2 := by
  obtain ⟨gs, c⟩ := p
  intro z hz
  rcases t with n | q | ab
  · rw [comb_inl, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hP
  · rw [comb_hash, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact T.Hz_fl_mono (fun q' hq => T.fl_subset_logH _ _ _ q' hq) none _
      (T.Hz_mono gs.fl none (fun t v hv => T.cache_persist _ c t v hv y hy) hP)
  · rw [comb_rev, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact T.Hz_mono gs.fl none (fun t v hv => T.cache_persist _ c t v hv y hy) hP

/-! ## The tail: walk, completion, secret -/

/-- The forged triple is a candidate only at a hidden position. -/
def heOf (gs : GS T.m St Blk) (o : Fin T.m × ℕ × Y) : Option (Fin T.m × ℕ × Y) :=
  if o.2.1 < gs.r o.1 then some o else none

theorem hz_he_le (gs : GS T.m St Blk) (c : T.C2) (h0 : ∀ a, gs.r a ≤ T.w + 1)
    (h1 : T.Inv1 gs.r c) (o : Fin T.m × ℕ × Y) :
    hz (T.Hz gs.fl (T.heOf gs o)) (T.Pot δ κ gs.fl (T.heOf gs o)) c ≤
      hz (T.Hz gs.fl none) (T.Pot δ κ gs.fl none) c + δ := by
  unfold heOf
  split_ifs with hlt
  · have hnone : c (.inr (o.1, T.ix o.2.1)) = none := by
      cases h : c (.inr (o.1, T.ix o.2.1)) with
      | none => rfl
      | some u =>
        have h2 := h1 o.1 (T.ix o.2.1) (by rw [h]; rfl)
        have h3 : (T.ix o.2.1).val ≤ o.2.1 := by simp [ix]
        have := h0 o.1
        omega
    have hHE : ¬ T.HEc (some o) c := by
      rintro ⟨a, j, x, he, u, hu, -⟩
      simp only [Option.some.injEq] at he
      subst he
      rw [hnone] at hu; cases hu
    have hHE0 : ¬ T.HEc none c := by rintro ⟨a, j, x, he, -⟩; cases he
    have hiff : T.Hz gs.fl (some o) c ↔ T.Hz gs.fl none c := by
      unfold Hz
      exact or_congr_right (or_congr_right ⟨fun h => absurd h hHE, fun h => absurd h hHE0⟩)
    by_cases hH : T.Hz gs.fl none c
    · rw [hz_of_P hH, hz_of_P (hiff.2 hH)]; exact le_self_add
    · rw [hz_of_not_P hH, hz_of_not_P (fun h => hH (hiff.1 h))]
      unfold Pot
      have hp0 : propInd (T.pHE none c) = 0 :=
        propInd_eq_zero_iff.2 fun h => by obtain ⟨a, j, x, he, -⟩ := h; cases he
      have hp1 : propInd (T.pHE (some o) c) ≤ 1 := by unfold propInd; split_ifs <;> simp
      rw [hp0, mul_zero, add_zero]
      calc _ ≤ δ * (gs.fl.countP fun q => decide (T.pGF c q) : ℕ) +
            δ * ((Finset.univ.filter fun q => T.pHit c q).card : ℕ) + δ * 1 +
            κ * (gs.fl.countP fun q => decide (T.isKey q) : ℕ) := by gcongr
        _ = _ := by ring
  · exact le_self_add

/-- **The secret draw.** -/
theorem draw_le (hκ : ∀ k0 : K, Pr{let k ← ($ᵗ K : ProbComp K)}[k = k0] ≤ κ)
    (o : Fin T.m × ℕ × Y) (gs : GS T.m St Blk) (wl : List ((St × Blk) × St)) (sv : T.HIdx → St)
    (c2 : T.C2) (F1 : ∀ i, c2 (.inr i) = some (sv i))
    (F2 : ∀ e ∈ gs.hl ++ wl, c2 (.inl e.1) = some e.2) :
    Pr{let k ← ($ᵗ K : ProbComp K)}[T.Efin o gs wl k sv] ≤
      hz (T.Hz gs.fl (T.heOf gs o)) (T.Pot δ κ gs.fl (T.heOf gs o)) c2 := by
  by_cases hH : T.Hz gs.fl (T.heOf gs o) c2
  · rw [hz_of_P hH]; exact prEvent_le_one _
  rw [hz_of_not_P hH]
  have himp : ∀ k, T.Efin o gs wl k sv → ∃ q ∈ gs.fl, T.isGK k q := by
    intro k h
    rcases h with ⟨q, hq, hc, a, j, x, hp, hj, hx⟩ | hgk | ⟨e, he, hc, a, j, x, hp, hj, hout⟩ |
      ⟨hlt, hx⟩
    · exact absurd (.inl ⟨q, hq, a, j, x, (T.chS_eq_some).2 ⟨hc, hp, hj⟩, sv _, F1 _, hx⟩) hH
    · exact hgk
    · exact absurd (.inr (.inl ⟨e.1, a, j, x, (T.chS_eq_some).2 ⟨hc, hp, hj⟩, e.2, sv _, F2 e he,
        F1 _, hout⟩)) hH
    · exact absurd (.inr (.inr ⟨o.1, o.2.1, o.2.2, by simp [heOf, hlt], sv _, F1 _, hx⟩)) hH
  refine (prEvent_mono _ _ _ himp).trans ?_
  refine (prEvent_exists_list_le_countP _ gs.fl (fun q k => T.isGK k q) T.isKey κ fun q => ?_).trans
    ?_
  · by_cases hk : T.isKey q
    · obtain ⟨hc, a0, k0, hp⟩ := hk
      rw [propInd_eq_one_iff.2 ⟨hc, a0, k0, hp⟩, mul_one]
      refine (prEvent_mono _ _ _ fun k hk => ?_).trans (hκ k0)
      obtain ⟨-, a, hp'⟩ := hk
      rw [hp] at hp'
      cases hp'
      rfl
    · rw [prEvent_eq_zero_of_forall_not _ _ fun k hk' => hk ⟨hk'.1, _, k, hk'.2.choose_spec⟩]
      exact zero_le
  · unfold Pot
    exact le_add_self

theorem prEvent_bind_eq_ex {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    Pr{let z ← mx >>= f}[p z] = ex mx fun x => Pr{let z ← f x}[p z] := by
  rw [prEvent_eq_ex, ex_bind]
  simp only [prEvent_eq_ex]

/-- **The tail of the deferred game.** -/
theorem tail_le (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (hκ : ∀ k0 : K, Pr{let k ← ($ᵗ K : ProbComp K)}[k = k0] ≤ κ)
    (gs : GS T.m St Blk) (c : T.C2) (hI : T.IA (gs, c)) (o : Fin T.m × ℕ × Y) :
    Pr{let z ← (simulateQ (T.spec2).romImpl (do
        let wv ← T.walkX gs.r o.1 o.2.1 (T.w - o.2.1) o.2.2
        let sv ← T.compS
        let k ← (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + T.spec2) K)
        pure (decide (T.Efin o gs wv.2 k sv)))).run' c}[z = true] ≤
      hz (T.Hz gs.fl none) (T.Pot δ κ gs.fl none) c + (T.w + 1) * δ := by
  obtain ⟨h0, h1, h3⟩ := hI
  have heq : (simulateQ (T.spec2).romImpl (do
        let wv ← T.walkX gs.r o.1 o.2.1 (T.w - o.2.1) o.2.2
        let sv ← T.compS
        let k ← (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + T.spec2) K)
        pure (decide (T.Efin o gs wv.2 k sv)))).run' c =
      (simulateQ (T.spec2).romImpl (T.walkX gs.r o.1 o.2.1 (T.w - o.2.1) o.2.2)).run c >>= fun w1 =>
        (simulateQ (T.spec2).romImpl T.compS).run w1.2 >>= fun s1 =>
          ($ᵗ K : ProbComp K) >>= fun k => pure (decide (T.Efin o gs w1.1.2 k s1.1)) := by
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure,
      StateT.run_pure, map_pure, simulateQ_romImpl_liftM_run, bind_map_left]
  rw [heq, prEvent_bind_eq_ex]
  refine (ex_mono_of_support _ (g := fun w1 => hz (T.Hz gs.fl none) (T.Pot δ κ gs.fl none) w1.2 + δ)
    fun w1 hw1 => ?_).trans ?_
  · obtain ⟨hI1, hlog⟩ := T.walk_supp gs.r o.1 _ _ _ c h1 w1 hw1
    rw [prEvent_bind_eq_ex]
    refine (ex_mono_of_support _ (g := fun s1 => hz (T.Hz gs.fl (T.heOf gs o))
      (T.Pot δ κ gs.fl (T.heOf gs o)) s1.2) fun s1 hs1 => ?_).trans ?_
    · refine (le_of_eq ?_).trans (T.draw_le κ hκ o gs w1.1.2 s1.1 s1.2
        (T.compS_supp w1.2 s1 hs1) fun e he => ?_)
      · rw [bind_pure_comp, prEvent_map]; simp only [Function.comp_def, decide_eq_true_eq]
      · rcases List.mem_append.mp he with he | he
        · exact T.cache_persist _ w1.2 _ _ (T.cache_persist _ c _ _ (h3 e he) w1 hw1) s1 hs1
        · exact T.cache_persist _ w1.2 _ _ (hlog e he) s1 hs1
    · refine (T.rom_run_le κ hδ gs.fl (T.heOf gs o) _ 0 T.qb_compS w1.2).trans ?_
      rw [Nat.cast_zero, zero_mul, add_zero]
      exact T.hz_he_le κ gs w1.2 h0 hI1 o
  · rw [ex_add, ex_const]
    refine (add_le_add (T.rom_run_le κ hδ gs.fl none _ _ (T.qb_walkX gs.r o.1 _ _ _) c) le_rfl).trans
      ?_
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    calc ((T.w - o.2.1 : ℕ) : ℝ≥0∞) * δ + δ ≤ (T.w : ℝ≥0∞) * δ + δ := by
          gcongr; exact_mod_cast Nat.sub_le _ _
      _ = (T.w + 1) * δ := by ring

theorem hz_init : hz (T.Hz [] none) (T.Pot δ κ [] none) (∅ : T.C2) = 0 := by
  have hH : ¬ T.Hz [] none (∅ : T.C2) := by
    rintro (⟨q, hq, -⟩ | ⟨q, a, j, x, -, v, u, hv, -⟩ | ⟨a, j, x, he, -⟩)
    · cases hq
    · cases hv
    · cases he
  rw [hz_of_not_P hH]
  unfold Pot
  have h1 : (Finset.univ.filter fun q => T.pHit (∅ : T.C2) q).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro q - ⟨a, j, x, -, hs, -⟩; cases hs
  have h2 : propInd (T.pHE none (∅ : T.C2)) = 0 :=
    propInd_eq_zero_iff.2 fun h => by obtain ⟨a, j, x, he, -⟩ := h; cases he
  rw [h1, h2]
  simp

theorem IA_init : T.IA (T.gs0, ∅) := by
  refine ⟨fun _ => le_rfl, fun a j h => ?_, fun e he => ?_⟩
  · simp at h
  · simp [gs0] at he

/-- **The deferred game's bound.** -/
theorem G2_le (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ)
    (hκ : ∀ k0 : K, Pr{let k ← ($ᵗ K : ProbComp K)}[k = k0] ≤ κ)
    (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) (q : ℕ)
    (hq : IsQueryBoundP A (fun t => T.isHash t = true) q) :
    HP.prT ((simulateQ T.spec2.romImpl (T.G2P A)).run' ∅) ≤ q * max (2 * δ) κ + (T.w + 1) * δ := by
  have heq : (simulateQ T.spec2.romImpl (T.G2P A)).run' ∅ =
      (simulateQ T.comb A).run (T.gs0, ∅) >>= fun p =>
        (simulateQ (T.spec2).romImpl (do
          let wv ← T.walkX p.2.1.r p.1.1 p.1.2.1 (T.w - p.1.2.1) p.1.2.2
          let sv ← T.compS
          let k ← (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + T.spec2) K)
          pure (decide (T.Efin p.1 p.2.1 wv.2 k sv)))).run' p.2.2 := by
    unfold G2P
    rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, comb_run, bind_map_left, map_bind]
    rfl
  unfold HP.prT
  rw [heq, prEvent_bind_eq_ex]
  refine (ex_mono_of_support _ (g := fun p => hz (fun p => T.Hz p.1.fl none p.2)
    (fun p => T.Pot δ κ p.1.fl none p.2) p.2 + (T.w + 1) * δ) fun p hp => ?_).trans ?_
  · have hI : T.IA p.2 := simulateQ_run_preservesInv T.comb T.IA
      (fun t s hs z hz => T.comb_IA t s hs z hz) A (T.gs0, ∅) T.IA_init p hp
    exact T.tail_le κ hδ hκ p.2.1 p.2.2 hI p.1
  · rw [ex_add, ex_const]
    refine add_le_add ?_ le_rfl
    refine (ex_hz_le_of_step T.comb T.IA (fun p => T.Hz p.1.fl none p.2)
      (fun p => T.Pot δ κ p.1.fl none p.2) _ (max (2 * δ) κ) (fun t s hs z hz => T.comb_IA t s hs z hz)
      (fun t s _ hs z hz => T.comb_abs t s hs z hz)
      (fun t s hs hP => T.comb_step κ hδ t s hs hP) A q hq (T.gs0, ∅) T.IA_init).trans
      (le_of_eq ?_)
    have h0 : hz (fun p : GS T.m St Blk × T.C2 => T.Hz p.1.fl none p.2)
        (fun p => T.Pot δ κ p.1.fl none p.2) (T.gs0, ∅) = 0 := T.hz_init κ
    rw [h0, zero_add]

/-! ## The headline -/

/-- **Milestone M0 (`status/DIRECT.md` §5.1).**  An adversary making at most `q` compression
queries (any number of reveals, any number of coins) wins the toy game with probability at most
`q · max (2δ) (1/|K|) + (w + 1) δ`, where `δ` bounds the probability that the output truncation
of a uniform chaining value is any fixed value.  There is no `m · q`, `w · q` or
`(#reveals) · q` term: each compression query is charged once, `2δ` if it is a chain block (a
guess of the hidden input or a hit on the next honest value, in either order) or `1/|K|` if it
is a secret-keyed block (a guess of the secret).  The `(w + 1) δ` is the experiment's own
evaluation of the chain from the forged value (`w` cells, a hit each) and the forged value
itself (equal to the hidden value at its position). -/
theorem toy_le (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) (q : ℕ)
    (hq : IsQueryBoundP A (fun t => T.isHash t = true) q) (δ : ℝ≥0∞)
    (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ) :
    T.realWin A ≤ q * max (2 * δ) (Fintype.card K : ℝ≥0∞)⁻¹ + (T.w + 1) * δ :=
  (T.realWin_le_G2 A).trans (T.G2_le _ hδ
    (fun k0 => (SampleableType.prEvent_uniformSample_eq_singleton k0).le) A q hq)

/-- The headline for a balanced truncation (`δ = 1/|Y|`) and a secret at least half as long as
an output (`|Y| ≤ 2|K|`): `(2q + w + 1)/|Y|`. -/
theorem toy_le_card (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) (q : ℕ)
    (hq : IsQueryBoundP A (fun t => T.isHash t = true) q) [Fintype Y]
    (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ (Fintype.card Y : ℝ≥0∞)⁻¹)
    (hKY : (Fintype.card Y : ℝ≥0∞) ≤ 2 * Fintype.card K) :
    T.realWin A ≤ (2 * q + T.w + 1) / Fintype.card Y := by
  refine (T.toy_le A q hq _ hδ).trans (le_of_eq ?_)
  have hmax : max (2 * (Fintype.card Y : ℝ≥0∞)⁻¹) (Fintype.card K : ℝ≥0∞)⁻¹ =
      2 * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
    refine max_eq_left ?_
    have h2 : (Fintype.card K : ℝ≥0∞)⁻¹ = 2 * (2 * (Fintype.card K : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    rw [h2]
    gcongr
  rw [hmax, div_eq_mul_inv]
  ring

end Params

end Ideal.Direct.Toy

#print axioms Ideal.Direct.Toy.Params.G2_le
#print axioms Ideal.Direct.Toy.Params.toy_le
#print axioms Ideal.Direct.Toy.Params.toy_le_card
