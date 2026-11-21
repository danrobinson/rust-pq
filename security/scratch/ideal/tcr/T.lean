import Ideal.Games.TcrDefs
import Ideal.Core.LazyLemmas
open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

section Lemmas

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-! ## Phase one: the invariant -/

/-- The phase-one invariant. -/
def TcrInv (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak)
    (s : SM_DT_TCR_State Tweak M) (c : Cache St Blk) : Prop :=
  (∀ t m m', (t, m) ∈ s.1 → (t, m') ∈ s.1 → m = m') ∧
  (∀ t m, (t, m) ∈ s.1 → (c (.inr (F.tch t m).1)).isSome) ∧
  (∀ B, (c (.inr B)).isSome →
    (∃ m, (btw B, m) ∈ s.1 ∧ B = (F.tch (btw B) m).1) ∨ btw B ∈ s.2) ∧
  (∀ t ∈ s.2, ∀ m, (t, m) ∉ s.1)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem TcrInv.congr_row {btw : Blk → Tweak} {s : SM_DT_TCR_State Tweak M}
    {c c' : Cache St Blk} (h : TcrInv F btw s c) (hc : ∀ B, c' (.inr B) = c (.inr B)) :
    TcrInv F btw s c' := by
  obtain ⟨ha, hb, hc', hd⟩ := h
  exact ⟨ha, fun t m hm => by rw [hc]; exact hb t m hm,
    fun B hB => hc' B (by rwa [hc] at hB), hd⟩

theorem run_tcrGameM_inl [DecidableEq Tweak] (n : ℕ) (s : SM_DT_TCR_State Tweak M)
    (c : Cache St Blk) :
    (simulateQ chainRO ((tcrGameM F (.inl n)).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$> ((chainRO (St := St) (Blk := Blk)) (.inl n)).run c := by
  simp [tcrGameM]

theorem run_tcrGameM_pub [DecidableEq Tweak] (q : St × Blk) (s : SM_DT_TCR_State Tweak M)
    (c : Cache St Blk) :
    (simulateQ chainRO ((tcrGameM F (.inr (.inl q))).run s)).run c =
      (fun p => ((p.1, s), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inl q))).run c := by
  simp [tcrGameM]

theorem run_tcrGameM_chal [DecidableEq Tweak] (tm : Tweak × M) (qs : List (Tweak × M))
    (tw : List Tweak) (c : Cache St Blk) :
    (simulateQ chainRO ((tcrGameM F (.inr (.inr (.inl tm)))).run (qs, tw))).run c =
      if F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 then
        pure ((none, qs, tw), c)
      else (fun p => ((some (F.out p.1), qs ++ [tm], tw), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.tch tm.1 tm.2)))).run c := by
  simp only [tcrGameM]
  by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;> simp [h]

theorem run_tcrGameM_coll [DecidableEq Tweak] (q : (i : ι) × Tweak × F.Msg i)
    (qs : List (Tweak × M)) (tw : List Tweak) (c : Cache St Blk) :
    (simulateQ chainRO ((tcrGameM F (.inr (.inr (.inr q)))).run (qs, tw))).run c =
      if TweakReserved (Q := Tweak × M) Prod.fst qs q.2.1 then
        pure ((none, qs, tw), c)
      else (fun p => ((some (F.cout q.1 p.1), qs, tw ++ [q.2.1]), p.2)) <$>
        ((chainRO (St := St) (Blk := Blk)) (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))).run c := by
  simp only [tcrGameM]
  by_cases h : TweakReserved (Q := Tweak × M) Prod.fst qs q.2.1 <;> simp [h]

/-- Every step of the SM-TCR game oracles preserves the invariant. -/
theorem tcrInv_step [DecidableEq Tweak] (btw : Blk → Tweak)
    (hbtwT : ∀ t m, btw (F.tch t m).1 = t) (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (t : F.advS.Domain) (s : SM_DT_TCR_State Tweak M) (c : Cache St Blk)
    (h : TcrInv F btw s c) :
    ∀ z ∈ support ((simulateQ chainRO ((tcrGameM F t).run s)).run c),
      TcrInv F btw z.1.2 z.2 := by
  intro z hz
  obtain ⟨qs, tw⟩ := s
  rcases t with n | q | tm | q
  · rw [run_tcrGameM_inl, chainRO_run_inl, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [support_map] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact h
  · rw [run_tcrGameM_pub, chainRO_run_pub, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact h.congr_row (row_eq_of_mem_support_randomOracle_pub q c hp)
  · rw [run_tcrGameM_chal] at hz
    split_ifs at hz with hcond
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · rw [support_map] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      obtain ⟨hsome, hrest⟩ := row_of_mem_support_chainRO_chain _ c hp
      obtain ⟨ha, hb, hc, hd⟩ := h
      rw [not_or, not_not] at hcond
      obtain ⟨-, hres, hntw⟩ := hcond
      obtain ⟨t₀, m₀⟩ := tm
      have hres' : ∀ m, (t₀, m) ∉ qs := fun m hm => hres ⟨(t₀, m), hm, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t m m' hm hm'
        simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm hm'
        rcases hm with hm | ⟨rfl, rfl⟩ <;> rcases hm' with hm' | ⟨ht, rfl⟩
        · exact ha t m m' hm hm'
        · exact absurd (ht ▸ hm) (hres' m)
        · exact absurd hm' (hres' m')
        · rfl
      · intro t m hm
        simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with hm | ⟨rfl, rfl⟩
        · by_cases hB : (F.tch t m).1 = (F.tch t₀ m₀).1
          · rw [hB]; exact hsome
          · rw [hrest _ hB]; exact hb t m hm
        · exact hsome
      · intro B hB
        by_cases hBB : B = (F.tch t₀ m₀).1
        · refine .inl ⟨m₀, ?_, ?_⟩
          · rw [hBB, hbtwT]; simp
          · rw [hBB, hbtwT]
        · rw [hrest B hBB] at hB
          rcases hc B hB with ⟨m, hm, hBm⟩ | htw
          · exact .inl ⟨m, List.mem_append_left _ hm, hBm⟩
          · exact .inr htw
      · intro t ht m hm
        simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with hm | ⟨rfl, rfl⟩
        · exact hd t ht m hm
        · exact hntw ht
  · rw [run_tcrGameM_coll] at hz
    split_ifs at hz with hcond
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · rw [support_map] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      obtain ⟨hsome, hrest⟩ := row_of_mem_support_chainRO_chain _ c hp
      obtain ⟨ha, hb, hc, hd⟩ := h
      obtain ⟨i, t₀, m₀⟩ := q
      have hres' : ∀ m, (t₀, m) ∉ qs := fun m hm => hcond ⟨(t₀, m), hm, rfl⟩
      refine ⟨ha, ?_, ?_, ?_⟩
      · intro t m hm
        by_cases hB : (F.tch t m).1 = (F.cch i t₀ m₀).1
        · rw [hB]; exact hsome
        · rw [hrest _ hB]; exact hb t m hm
      · intro B hB
        by_cases hBB : B = (F.cch i t₀ m₀).1
        · refine .inr ?_
          rw [hBB, hbtwC]; simp
        · rw [hrest B hBB] at hB
          rcases hc B hB with hm | htw
          · exact .inl hm
          · exact .inr (List.mem_append_left _ htw)
      · intro t ht m hm
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hd t ht m hm
        · exact hres' m hm

/-- The invariant holds after phase one. -/
theorem tcrInv_phase1 [DecidableEq Tweak] (btw : Blk → Tweak)
    (hbtwT : ∀ t m, btw (F.tch t m).1 = t) (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (A : TcrAdv F) :
    ∀ z ∈ support ((simulateQ (hS St Blk + tS St Blk).romImpl
      (simulateQ chainToT (tcrProg₁ A))).run ∅), TcrInv F btw z.1.2 z.2 :=
  chainRO_inv_of_step (tcrGameM F) (TcrInv F btw) (tcrInv_step btw hbtwT hbtwC) A.choose
    ([], []) ∅ ⟨by simp, by simp, fun B hB => by simp at hB, by simp⟩

/-! ## Phase two -/

/-- The good predicate of phase two, for a fixed target list: every target cell is cached, and
no other cached private-row cell with the same tweak has the same output. -/
def TcrGood (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak)
    (qs : List (Tweak × M)) (c : Cache St Blk) : Prop :=
  ∀ t m, (t, m) ∈ qs → ∃ v, c (.inr (F.tch t m).1) = some v ∧
    ∀ B u, c (.inr B) = some u → btw B = t → B ≠ (F.tch t m).1 → F.out u ≠ F.out v

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem TcrInv.good {btw : Blk → Tweak} {s : SM_DT_TCR_State Tweak M} {c : Cache St Blk}
    (h : TcrInv F btw s c) : TcrGood F btw s.1 c := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  intro t m hm
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hb t m hm)
  refine ⟨v, hv, fun B u hB hbt hne => absurd ?_ hne⟩
  rcases hc B (by rw [hB]; rfl) with ⟨m', hm', hBm⟩ | htw
  · rw [hbt] at hm' hBm
    rw [hBm, ha t m m' hm hm']
  · exact absurd hm (hd t (hbt ▸ htw) m)

omit [SampleableType St] in
/-- Caching a fresh public cell keeps the good predicate. -/
theorem TcrGood.cacheQuery_pub {btw : Blk → Tweak} {qs : List (Tweak × M)} {c : Cache St Blk}
    (h : TcrGood F btw qs c) (q : St × Blk) (u : St) :
    TcrGood F btw qs (c.cacheQuery (.inl q) u) := by
  have hrow : ∀ B, (c.cacheQuery (.inl q) u) (.inr B) = c (.inr B) := fun B =>
    QueryCache.cacheQuery_of_ne (t := .inl q) c u (by simp)
  intro t m hm
  obtain ⟨v, hv, hrest⟩ := h t m hm
  exact ⟨v, by rw [hrow, hv], fun B u' hB => hrest B u' (by rwa [hrow] at hB)⟩

/-- Caching a fresh private-row cell breaks the good predicate with probability at most `δ`. -/
theorem prEvent_not_tcrGood_cacheQuery_row_le {btw : Blk → Tweak} {qs : List (Tweak × M)}
    (hnd : ∀ t m m', (t, m) ∈ qs → (t, m') ∈ qs → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    {c : Cache St Blk} (h : TcrGood F btw qs c) (B : Blk) (hB : c (.inr B) = none) :
    Pr{let u ← ($ᵗ St : ProbComp St)}[¬ TcrGood F btw qs (c.cacheQuery (.inr B) u)] ≤ δ := by
  have hrow : ∀ (u : St) B', B' ≠ B → (c.cacheQuery (.inr B) u) (.inr B') = c (.inr B') :=
    fun u B' hB' => QueryCache.cacheQuery_of_ne (t := .inr B) c u (by simpa using hB')
  have hself : ∀ u : St, (c.cacheQuery (.inr B) u) (.inr B) = some u := fun u =>
    QueryCache.cacheQuery_self c (.inr B) u
  -- the general shape: good is kept unless the fresh answer matches a target with tweak `btw B`
  have key : ∀ u : St, (∀ m v, (btw B, m) ∈ qs → c (.inr (F.tch (btw B) m).1) = some v →
      F.out u ≠ F.out v) → TcrGood F btw qs (c.cacheQuery (.inr B) u) := by
    intro u hu t m hm
    obtain ⟨v, hv, hrest⟩ := h t m hm
    have hne : (F.tch t m).1 ≠ B := fun e => by rw [e, hB] at hv; exact absurd hv (by simp)
    refine ⟨v, by rw [hrow u _ hne, hv], fun B' u' hB' hbt hne' => ?_⟩
    by_cases hBB : B' = B
    · subst hBB
      rw [hself] at hB'
      obtain rfl : u = u' := Option.some.inj hB'
      subst hbt
      exact hu m v hm hv
    · rw [hrow u B' hBB] at hB'
      exact hrest B' u' hB' hbt hne'
  by_cases hex : ∃ m, (btw B, m) ∈ qs
  · obtain ⟨m₀, hm₀⟩ := hex
    obtain ⟨v₀, hv₀, -⟩ := h _ m₀ hm₀
    refine (prEvent_mono _ _ (fun u => F.out u = F.out v₀) fun u hu => ?_).trans (hδ _)
    by_contra hne
    refine hu (key u fun m v hm hv => ?_)
    obtain rfl := hnd _ _ _ hm hm₀
    rw [hv₀] at hv
    obtain rfl := Option.some.inj hv
    exact hne
  · rw [prEvent_eq_zero_of_forall_not _ _ fun u => not_not.mpr
      (key u fun m v hm _ => absurd ⟨m, hm⟩ hex)]
    exact zero_le

/-- With a single message block, a routed evaluation of the attacked member is one read of the
private row table (when `cv ≠ IV`). -/
theorem run_evalPub (hsingle : ∀ t m, (F.tch t m).2 = []) (seed : PkSeed) (cv : St)
    (hcv : cv ≠ F.IV) (t : Tweak) (m : M) (c : Cache St Blk) :
    (simulateQ (routeRO F.IV (F.sb seed) cv) (evalPub F seed t m)).run c =
      (fun p => (F.out p.1, p.2)) <$>
        ((hS St Blk + tS St Blk).randomOracle (.inr (F.tch t m).1)).run c := by
  have h : (cv, (F.tch t m).1) ≠ (F.IV, F.sb seed) := fun e => hcv (Prod.ext_iff.mp e).1
  simp only [evalPub, hsingle, List.foldlM_nil, simulateQ_bind, StateT.run_bind,
    simulateQ_spec_query, routeRO_run_seed, pure_bind, routeRO_run_row _ _ _ _ _ h,
    bind_pure_comp]
  simp only [map_pure, simulateQ_pure, StateT.run_pure, bind_pure_comp]
  rfl

/-- The winning condition, run from a good cache with `cv ≠ IV`, holds with probability at most
`δ`. -/
theorem prEvent_tcr_final_le [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (seed : PkSeed) (cv : St) (hcv : cv ≠ F.IV) {qs : List (Tweak × M)} {c : Cache St Blk}
    (hG : TcrGood F btw qs c) (t : Tweak) (m mj : M) (hmem : (t, mj) ∈ qs) :
    Pr{let b ← (simulateQ (routeRO F.IV (F.sb seed) cv) (do
        let y ← evalPub F seed t m
        let y' ← evalPub F seed t mj
        return decide (m ≠ mj ∧ y = y'))).run' c}[b = true] ≤ δ := by
  obtain ⟨vj, hvj, hrest⟩ := hG t mj hmem
  have hj : ∀ c' : Cache St Blk, c' (.inr (F.tch t mj).1) = some vj →
      ((hS St Blk + tS St Blk).randomOracle (.inr (F.tch t mj).1)).run c' = pure (vj, c') := by
    intro c' hc'
    rcases randomOracle_run_row_cases (F.tch t mj).1 c' with ⟨v', hv', h'⟩ | ⟨hn, -⟩
    · rw [hc'] at hv'
      obtain rfl := Option.some.inj hv'
      exact h'
    · rw [hc'] at hn
      exact absurd hn (by simp)
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, StateT.run_bind, run_evalPub hsingle seed cv hcv, simulateQ_pure,
    StateT.run_pure]
  rcases randomOracle_run_row_cases (F.tch t m).1 c with ⟨v, hv, h⟩ | ⟨hnone, h⟩
  · rw [h]
    simp only [map_pure, pure_bind, hj c hvj]
    have hfalse : ¬ (m ≠ mj ∧ F.out v = F.out vj) := fun ⟨hne, heq⟩ =>
      hrest _ v hv (hbtwT t m) (fun e => hne (hinj t m mj e)) heq
    simp [hfalse]
  · rw [h]
    have hne : (F.tch t mj).1 ≠ (F.tch t m).1 := fun e => by
      rw [e, hnone] at hvj; exact absurd hvj (by simp)
    have hj' : ∀ u : St, (c.cacheQuery (.inr (F.tch t m).1) u) (.inr (F.tch t mj).1) = some vj :=
      fun u => by
        rw [QueryCache.cacheQuery_of_ne (t := .inr (F.tch t m).1) c u (by simpa using hne), hvj]
    simp only [map_bind, bind_map_left, Functor.map_map, hj _ (hj' _), map_pure, pure_bind]
    simp only [bind_pure_comp]
    exact (prEvent_mono ($ᵗ St) _ (fun u => F.out u = F.out vj)
      fun u (hu : decide (m ≠ mj ∧ F.out u = F.out vj) = true) =>
        (of_decide_eq_true hu).2).trans (hδ _)

/-- Phase two, run from a cache satisfying the phase-one invariant with `cv ≠ IV`, returns
`true` with probability at most `(q₂ + 1) * δ`. -/
theorem prEvent_tcr_phase2_le [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂)
    (x : A.State × SM_DT_TCR_State Tweak M) (c : Cache St Blk) (seed : PkSeed) (cv : St)
    (hInv : TcrInv F btw x.2 c) (hcv : cv ≠ F.IV) :
    Pr{let b ← (simulateQ (routeRO F.IV (F.sb seed) cv) (tcrP₂ A seed x)).run' c}[b = true] ≤
      (q₂ + 1 : ℕ) * δ := by
  classical
  have hG := hInv.good
  unfold tcrP₂
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine (prEvent_bind_le_prEvent_add _ _ (fun z => ¬ TcrGood F btw x.2.1 z.2) _ (ε := δ)
    fun z hz => ?_).trans ?_
  · rw [not_not] at hz
    obtain ⟨⟨j, m⟩, c₂⟩ := z
    rw [← StateT.run'_eq]
    dsimp only
    cases hj : x.2.1[j]? with
    | none =>
      simp
    | some tm =>
      obtain ⟨t, mj⟩ := tm
      exact prEvent_tcr_final_le hsingle btw hbtwT hinj δ hδ seed cv hcv hz t m mj
        (List.mem_of_getElem? hj)
  · refine (add_le_add_left (prEvent_routeRO_bad_le F.IV (F.sb seed) cv
      (fun c => ¬ TcrGood F btw x.2.1 c) δ
      (fun c q u hc _ => not_not.mpr ((not_not.mp hc).cacheQuery_pub q u))
      (fun c B hc hB => prEvent_not_tcrGood_cacheQuery_row_le hInv.1 δ hδ (not_not.mp hc) B hB)
      (A.forge x.1 seed) q₂ (hq₂ x.1 seed) c (not_not.mpr hG)) _).trans (le_of_eq ?_)
    push_cast
    ring

end Lemmas

theorem tcr_ideal_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hsingle : ∀ t m, (F.tch t m).2 = [])
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hinj : ∀ t m m', (F.tch t m).1 = (F.tch t m').1 → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂) :
    𝒟[idealGame F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)] {true} ≤
      (q₂ + 1 : ℕ) * δ + (Fintype.card St : ℝ≥0∞)⁻¹ :=
  idealGame_le_of_inv F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)
    (fun x c => TcrInv F btw x.2 c) _ (tcrInv_phase1 btw hbtwT hbtwC A)
    fun x c seed cv hInv hcv =>
      prEvent_tcr_phase2_le hsingle btw hbtwT hinj δ hδ A q₂ hq₂ x c seed cv hInv hcv

end Ideal
