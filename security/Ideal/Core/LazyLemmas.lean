import Ideal.Core.Defs
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.EvalDist.ProbabilityBounds

/-!
# Game-independent lemmas about the lazy ideal game

* `prEvent_bad_le_of_step`: the step bound.  If every `p`-step of a stateful handler makes a bad
  predicate fire with probability at most `ε` from a non-bad state and the other steps never do,
  a computation with at most `n` `p`-queries ends in a bad state with probability `≤ n * ε`.
* `chainRO`, `routeRO`: the phase-one handler `chainToT` and the phase-two handler `route`
  fused with the lazy random oracle `romImpl` into handlers with state the joint cache; their
  step shapes (`chainRO_run_*`, `routeRO_run_*`).
* `prEvent_routeRO_bad_le`: the step bound specialised to phase two: a bad predicate of the
  cache that only a fresh private-row cell can fire, with probability `≤ ε`.
* `chainRO_inv_of_step`: an invariant relating the state of a phase-one game handler and the
  cache holds after phase one as soon as every game step preserves it.
* `idealGame_le_of_inv`: the ideal game is won with probability at most `ε + 1/|St|` when an
  invariant of phase one bounds the phase-two winning probability by `ε` for every `cv ≠ IV`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

/-! ## The step bound -/

section StepBound

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- **Step bound.**  `bad` is a predicate on the state of the handler `so`, and `p` marks the
charged queries.  If from a non-bad state a `p`-step ends in a bad state with probability at most
`ε` and a non-`p`-step never does, then a computation making at most `n` `p`-queries, run from a
non-bad state, ends in a bad state with probability at most `n * ε`. -/
theorem prEvent_bad_le_of_step (so : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (p : ι → Prop) [DecidablePred p] (ε : ℝ≥0∞)
    (hp : ∀ t s, ¬ bad s → p t → Pr{let z ← (so t).run s}[bad z.2] ≤ ε)
    (hnp : ∀ t s, ¬ bad s → ¬ p t → ∀ z ∈ support ((so t).run s), ¬ bad z.2)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) (hs : ¬ bad s) :
    Pr{let z ← (simulateQ so oa).run s}[bad z.2] ≤ n * ε := by
  classical
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure]
    simp only [hs, ↓reduceIte]
    exact zero_le
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [run_simulateQ_query_bind]
    by_cases hpt : p t
    · simp only [hpt, ↓reduceIte] at hn
      have hn0 : 0 < n := by simpa using hn.1
      refine (prEvent_bind_le_prEvent_add ((so t).run s)
        (fun us => (simulateQ so (k us.1)).run us.2) (fun us => bad us.2) (fun z => bad z.2)
        (ε := (n - 1 : ℕ) * ε) fun us hus => ih us.1 (n - 1) (hn.2 us.1) us.2 hus).trans ?_
      refine (add_le_add_left (hp t s hs hpt) _).trans (le_of_eq ?_)
      obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [hpt, ↓reduceIte] at hn
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun us hus =>
        ih us.1 n (hn.2 us.1) us.2 (hnp t s hs hpt us hus)

end StepBound

/-! ## The fused handlers -/

section Fused

variable {St Blk : Type} [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- The joint cache of the public table and the private row table. -/
abbrev Cache (St Blk : Type) := (hS St Blk + tS St Blk).QueryCache

/-- Phase one fused with the lazy oracle: a handler on the joint cache. -/
noncomputable def chainRO :
    QueryImpl (unifSpec + (hS St Blk + chainS St Blk)) (StateT (Cache St Blk) ProbComp) :=
  (hS St Blk + tS St Blk).romImpl ∘ₛ chainToT

/-- Phase two fused with the lazy oracle: a handler on the joint cache. -/
noncomputable def routeRO (IV : St) (sbSeed : Blk) (cv : St) :
    QueryImpl (unifSpec + hS St Blk) (StateT (Cache St Blk) ProbComp) :=
  (hS St Blk + tS St Blk).romImpl ∘ₛ route IV sbSeed cv

theorem simulateQ_romImpl_chainToT {α : Type}
    (oa : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α) :
    simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ chainToT oa) = simulateQ chainRO oa :=
  (QueryImpl.simulateQ_compose _ _ oa).symm

theorem simulateQ_romImpl_route (IV : St) (sbSeed : Blk) (cv : St) {α : Type}
    (oa : OracleComp (unifSpec + hS St Blk) α) :
    simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ (route IV sbSeed cv) oa) =
      simulateQ (routeRO IV sbSeed cv) oa :=
  (QueryImpl.simulateQ_compose _ _ oa).symm

/-- A lazy-oracle step at a public cell either returns the cached answer or samples and caches
a fresh one. -/
theorem randomOracle_run_pub_cases (q : St × Blk) (c : Cache St Blk) :
    (∃ v : St, c (.inl q) = some v ∧
      ((hS St Blk + tS St Blk).randomOracle (.inl q)).run c = pure (v, c)) ∨
    (c (.inl q) = none ∧ ((hS St Blk + tS St Blk).randomOracle (.inl q)).run c =
      (fun u : St => (u, c.cacheQuery (.inl q) u)) <$> ($ᵗ St : ProbComp St)) := by
  rw [randomOracle.run_eq]
  cases h : c.toFn (.inl q) with
  | none => exact .inr ⟨rfl, by simp [map_eq_bind_pure_comp]⟩
  | some v => exact .inl ⟨v, rfl, rfl⟩

/-- A lazy-oracle step at a private-row cell either returns the cached answer or samples and
caches a fresh one. -/
theorem randomOracle_run_row_cases (B : Blk) (c : Cache St Blk) :
    (∃ v : St, c (.inr B) = some v ∧
      ((hS St Blk + tS St Blk).randomOracle (.inr B)).run c = pure (v, c)) ∨
    (c (.inr B) = none ∧ ((hS St Blk + tS St Blk).randomOracle (.inr B)).run c =
      (fun u : St => (u, c.cacheQuery (.inr B) u)) <$> ($ᵗ St : ProbComp St)) := by
  rw [randomOracle.run_eq]
  cases h : c.toFn (.inr B) with
  | none => exact .inr ⟨rfl, by simp [map_eq_bind_pure_comp]⟩
  | some v => exact .inl ⟨v, rfl, rfl⟩

theorem routeRO_run_inl (IV : St) (sbSeed : Blk) (cv : St) (n : ℕ) (c : Cache St Blk) :
    (routeRO IV sbSeed cv (.inl n)).run c =
      (fun u => (u, c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [routeRO, route, QueryImpl.apply_compose]
  exact roSim.run_liftM _ (unifSpec.query n : ProbComp (Fin (n + 1))) c

theorem routeRO_run_seed (IV : St) (sbSeed : Blk) (cv : St) (c : Cache St Blk) :
    (routeRO IV sbSeed cv (.inr (IV, sbSeed))).run c = pure (cv, c) := by
  simp [routeRO, route, QueryImpl.apply_compose]

theorem routeRO_run_row (IV : St) (sbSeed : Blk) (cv : St) (B : Blk) (c : Cache St Blk)
    (h : (cv, B) ≠ (IV, sbSeed)) :
    (routeRO IV sbSeed cv (.inr (cv, B))).run c =
      ((hS St Blk + tS St Blk).randomOracle (.inr B)).run c := by
  simp [routeRO, route, QueryImpl.apply_compose, h]

theorem routeRO_run_pub (IV : St) (sbSeed : Blk) (cv : St) (q : St × Blk) (c : Cache St Blk)
    (h : q ≠ (IV, sbSeed)) (h' : q.1 ≠ cv) :
    (routeRO IV sbSeed cv (.inr q)).run c =
      ((hS St Blk + tS St Blk).randomOracle (.inl q)).run c := by
  simp [routeRO, route, QueryImpl.apply_compose, h, h']

theorem chainRO_run_inl (n : ℕ) (c : Cache St Blk) :
    ((chainRO (St := St) (Blk := Blk)) (.inl n)).run c =
      (fun u => (u, c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [chainRO, chainToT, QueryImpl.apply_compose]
  exact roSim.run_liftM _ (unifSpec.query n : ProbComp (Fin (n + 1))) c

theorem chainRO_run_pub (q : St × Blk) (c : Cache St Blk) :
    ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c =
      ((hS St Blk + tS St Blk).randomOracle (.inl q)).run c := by
  simp [chainRO, chainToT, QueryImpl.apply_compose]

theorem chainRO_run_chain (q : Blk × List Blk) (c : Cache St Blk) :
    ((chainRO (St := St) (Blk := Blk)) (.inr (.inr q))).run c =
      ((hS St Blk + tS St Blk).randomOracle (.inr q.1)).run c >>= fun z =>
        (simulateQ (hS St Blk + tS St Blk).romImpl
          (q.2.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))
            z.1)).run z.2 := by
  simp [chainRO, chainToT, QueryImpl.apply_compose]

/-! ### Which cells a step can change -/

/-- A public-cell step leaves the private row table unchanged. -/
theorem row_eq_of_mem_support_randomOracle_pub (q : St × Blk) (c : Cache St Blk)
    {z : St × Cache St Blk}
    (hz : z ∈ support (((hS St Blk + tS St Blk).randomOracle (.inl q)).run c)) (B : Blk) :
    z.2 (.inr B) = c (.inr B) := by
  rcases randomOracle_run_pub_cases q c with ⟨v, -, h⟩ | ⟨-, h⟩
  · rw [h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · rw [h, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_of_ne (t := .inl q) c u (by simp)

/-- A private-row step caches its cell and leaves the other private-row cells unchanged. -/
theorem row_of_mem_support_randomOracle_row (B : Blk) (c : Cache St Blk)
    {z : St × Cache St Blk}
    (hz : z ∈ support (((hS St Blk + tS St Blk).randomOracle (.inr B)).run c)) :
    z.2 (.inr B) = some z.1 ∧ ∀ B', B' ≠ B → z.2 (.inr B') = c (.inr B') := by
  rcases randomOracle_run_row_cases B c with ⟨v, hv, h⟩ | ⟨-, h⟩
  · rw [h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨hv, fun _ _ => rfl⟩
  · rw [h, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨QueryCache.cacheQuery_self c (.inr B) u,
      fun B' hB' => QueryCache.cacheQuery_of_ne (t := .inr B) c u (by simpa using hB')⟩

/-- A fold of public queries leaves the private row table unchanged. -/
theorem row_eq_of_mem_support_foldlM_pub (bs : List Blk) (c₀ : St) (c : Cache St Blk)
    {z : St × Cache St Blk}
    (hz : z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (bs.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b))))
        c₀)).run c)) (B : Blk) :
    z.2 (.inr B) = c (.inr B) := by
  induction bs generalizing c₀ c with
  | nil =>
    simp only [List.foldlM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  | cons b bs ih =>
    simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [ih _ _ hz]
    refine row_eq_of_mem_support_randomOracle_pub (c₀, b) c ?_ B
    simpa using hy

/-- A chain step of phase one caches the private-row cell of its first block and leaves the
other private-row cells unchanged. -/
theorem row_of_mem_support_chainRO_chain (q : Blk × List Blk) (c : Cache St Blk)
    {z : St × Cache St Blk}
    (hz : z ∈ support (((chainRO (St := St) (Blk := Blk)) (.inr (.inr q))).run c)) :
    (z.2 (.inr q.1)).isSome ∧ ∀ B', B' ≠ q.1 → z.2 (.inr B') = c (.inr B') := by
  rw [chainRO_run_chain, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  have h1 := row_of_mem_support_randomOracle_row q.1 c hy
  have h2 := row_eq_of_mem_support_foldlM_pub q.2 y.1 y.2 hz
  exact ⟨by rw [h2, h1.1]; rfl, fun B' hB' => by rw [h2, h1.2 B' hB']⟩

/-! ### Phase one: invariants -/

/-- **Phase-one invariant.**  A relation `Inv` between the state of a game handler `inner`
(over the keyed-chain interface) and the joint cache holds after running any computation
through `inner`, `chainToT` and the lazy oracle, as soon as it is preserved by each `inner`
step run through the fused handler `chainRO`. -/
theorem chainRO_inv_of_step {ι₀ : Type} {spec₀ : OracleSpec ι₀} {σ α : Type}
    (inner : QueryImpl spec₀
      (StateT σ (OracleComp (unifSpec + (hS St Blk + chainS St Blk)))))
    (Inv : σ → Cache St Blk → Prop)
    (hstep : ∀ t s c, Inv s c →
      ∀ z ∈ support ((simulateQ chainRO ((inner t).run s)).run c), Inv z.1.2 z.2)
    (oa : OracleComp spec₀ α) (s : σ) (c : Cache St Blk) (h : Inv s c) :
    ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT ((simulateQ inner oa).run s))).run c), Inv z.1.2 z.2 := by
  intro z hz
  rw [simulateQ_romImpl_chainToT] at hz
  exact simulateQ_run_simulateQ_run_preservesInv chainRO inner Inv hstep oa s c h hz

/-! ### Phase two: the step bound -/

/-- **Phase-two step bound.**  A bad predicate of the cache that caching a fresh public cell
never fires and caching a fresh private-row cell fires with probability at most `ε` holds
after a phase-two computation making at most `n` compression queries, run from a non-bad
cache, with probability at most `n * ε`. -/
theorem prEvent_routeRO_bad_le (IV : St) (sbSeed : Blk) (cv : St) (bad : Cache St Blk → Prop)
    (ε : ℝ≥0∞)
    (hpub : ∀ (c : Cache St Blk) (q : St × Blk) (u : St), ¬ bad c → c (.inl q) = none →
      ¬ bad (c.cacheQuery (.inl q) u))
    (hrow : ∀ (c : Cache St Blk) (B : Blk), ¬ bad c → c (.inr B) = none →
      Pr{let u ← ($ᵗ St : ProbComp St)}[bad (c.cacheQuery (.inr B) u)] ≤ ε)
    {α : Type} (oa : OracleComp (unifSpec + hS St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (c : Cache St Blk) (hc : ¬ bad c) :
    Pr{let z ← (simulateQ (routeRO IV sbSeed cv) oa).run c}[bad z.2] ≤ n * ε := by
  classical
  refine prEvent_bad_le_of_step _ bad _ ε ?_ ?_ oa n hn c hc
  · rintro (n | q) s hs ht
    · simp at ht
    · have hpure : ∀ v : St, Pr{let z ← (pure (v, s) : ProbComp (St × Cache St Blk))}[bad z.2]
          ≤ ε := fun v => by
        rw [prEvent_pure]
        simp only [hs, ↓reduceIte]
        exact zero_le
      by_cases h1 : q = (IV, sbSeed)
      · subst h1
        rw [routeRO_run_seed]
        exact hpure cv
      · by_cases h2 : q.1 = cv
        · obtain ⟨c', B⟩ := q
          subst h2
          rw [routeRO_run_row _ _ _ _ _ h1]
          rcases randomOracle_run_row_cases B s with ⟨v, -, h⟩ | ⟨hnone, h⟩
          · rw [h]
            exact hpure v
          · rw [h, prEvent_map]
            exact hrow s B hs hnone
        · rw [routeRO_run_pub _ _ _ _ _ h1 h2]
          rcases randomOracle_run_pub_cases q s with ⟨v, -, h⟩ | ⟨hnone, h⟩
          · rw [h]
            exact hpure v
          · rw [h, prEvent_map, prEvent_eq_zero_of_forall_not _ _ fun u => hpub s q u hs hnone]
            exact zero_le
  · rintro (n | q) s hs ht z hz
    · rw [routeRO_run_inl, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact hs
    · simp at ht

/-! ### The ideal game from a phase-one invariant -/

/-- **Decomposition of the ideal game.**  If `Inv` holds of the phase-one output and the cache
after phase one, and for every `cv ≠ IV` phase two run from such an output and cache returns
`true` with probability at most `ε`, the ideal game returns `true` with probability at most
`ε + 1/|St|`. -/
theorem idealGame_le_of_inv [Fintype St] {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool)
    (Inv : σ → Cache St Blk → Prop) (ε : ℝ≥0∞)
    (h1 : ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT prog₁)).run ∅), Inv z.1 z.2)
    (h2 : ∀ x c seed cv, Inv x c → cv ≠ IV →
      Pr{let b ← (simulateQ (routeRO IV (sb seed) cv) (P₂ seed x)).run' c}[b = true] ≤ ε) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] {true} ≤ ε + (Fintype.card St : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton]
  unfold idealGame idealProg
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  have hInv := h1 z hz
  rw [← StateT.run'_eq, simulateQ_bind, roSim.run'_liftM_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun seed => ?_
  rw [simulateQ_bind, roSim.run'_liftM_bind]
  refine (prEvent_bind_le_prEvent_add _ _ (fun cv => cv = IV) _ (ε := ε) fun cv hcv => ?_).trans ?_
  · rw [simulateQ_romImpl_route]
    exact h2 z.1 z.2 seed cv hInv hcv
  · rw [SampleableType.prEvent_uniformSample_eq_singleton, add_comm]

end Fused

end Ideal

#print axioms Ideal.prEvent_bad_le_of_step
#print axioms Ideal.chainRO_inv_of_step
#print axioms Ideal.prEvent_routeRO_bad_le
#print axioms Ideal.idealGame_le_of_inv
#print axioms Ideal.row_of_mem_support_chainRO_chain
