import Ideal.Games.TcrMultiSym
import Ideal.Games.TcrMultiBuild
import Ideal.Games.TcrBridge
import Ideal.Core.HPFlag
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

/-!
# Multi-block SM-TCR in the ideal-compression model: phase one

`tcr_multi_phase1_le`: after phase one of the ideal game the invariant `MInv` holds of the target
list and the joint cache, and the cache has boundedly many cells, except with probability
`O(Q²)/|St|` — given that the eager symbolic game `symE` dominates the real phase one `conG`
through `fbuild` until the hidden values stop being `Nice` (hypothesis `hdom`).

Proof.  The real phase one is a run of `conG F` (`MP1.fuse_run`); by `hdom` its event is at most
the event read through `fbuild`, or `¬ Nice`, in the run of `symE`; drawing the hidden values at
the end instead (`MP1.intertwines_fillS`) this is the run of the single-block game `symD`
followed by `drawN`; the single-block cache is injective without `IV` values except with
probability `N(N+1)/|St|` (`MP1.prEvent_flat_not_gd_le`), and then the drawn values are
`FillNice` except with the probability of `prEvent_drawN_not_fillNice`, in which case
`build_good` applies.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type}

namespace MP1

section

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-! ## The fused handler -/

theorem fuse_run {ι₀ : Type} {spec₀ : OracleSpec ι₀} {σ α : Type}
    (inner : QueryImpl spec₀ (StateT σ (OracleComp (gS St Blk)))) (oa : OracleComp spec₀ α)
    (s : σ) (c : Cache St Blk) :
    (simulateQ chainRO ((simulateQ inner oa).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (fuse inner) oa).run (s, c) := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure x => simp
  | query_bind t k ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind]
    simp only [fuse, StateT.run_mk, map_bind, bind_map_left]
    exact bind_congr fun y => ih y.1.1 y.1.2 y.2

theorem run_fuse_eq {ι₀ : Type} {spec₀ : OracleSpec ι₀} {σ α : Type}
    (inner : QueryImpl spec₀ (StateT σ (OracleComp (gS St Blk)))) (oa : OracleComp spec₀ α)
    (s : σ) (c : Cache St Blk) :
    (simulateQ (fuse inner) oa).run (s, c) =
      (fun y => (y.1.1, (y.1.2, y.2))) <$>
        (simulateQ chainRO ((simulateQ inner oa).run s)).run c := by
  rw [fuse_run, Functor.map_map]
  simp

/-- A run through `chainRO` only extends the cache. -/
theorem chainRO_le {α : Type} (oa : OracleComp (gS St Blk) α) (c : Cache St Blk)
    {z : α × Cache St Blk} (hz : z ∈ support ((simulateQ chainRO oa).run c)) : c ≤ z.2 := by
  rw [← simulateQ_romImpl_chainToT] at hz
  exact le_snd_of_mem_support_run_unifFwdImpl_add_withCaching _ _ hz

theorem CLe_of_le {c c' : Cache St Blk} (h : c ≤ c') : CLe (look c) (look c') := by
  intro x v hx
  cases x with
  | inl q => exact h hx
  | inr B => exact h hx

theorem CFin_mono {κ : Cell St Blk → Option St} {n m : ℕ} (h : CFin κ n) (hnm : n ≤ m) :
    CFin κ m := by
  obtain ⟨l, hl, hx⟩ := h
  exact ⟨l, hl.trans hnm, hx⟩

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem Nice_mono {κ κ' : Cell St Blk → Option St} {hs : List (List St)} (h : List St)
    (hle : CLe κ κ') (hN : Nice κ' (hs ++ [h])) : Nice κ hs := by
  obtain ⟨h1, h2⟩ := hN
  rw [List.flatten_append] at h1 h2
  refine ⟨(List.nodup_append.mp h1).1, fun x hx b => ?_⟩
  have := h2 x (List.mem_append_left _ hx) b
  cases hk : κ (.inl (x, b)) with
  | none => rfl
  | some v => rw [hle _ _ hk] at this; exact absurd this (by simp)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem Nice_mono' {κ κ' : Cell St Blk → Option St} {hs : List (List St)}
    (hle : CLe κ κ') (hN : Nice κ' hs) : Nice κ hs := by
  obtain ⟨h1, h2⟩ := hN
  refine ⟨h1, fun x hx b => ?_⟩
  have := h2 x hx b
  cases hk : κ (.inl (x, b)) with
  | none => rfl
  | some v => rw [hle _ _ hk] at this; exact absurd this (by simp)

/-! ## Steps of the single-block game -/

variable [DecidableEq Tweak] {F : THFam St Blk PkSeed Tweak M Y ι}

/-- The target list after a step of the single-block game: unchanged unless the query is an
accepted challenge query, which appends a target with a fresh tweak. -/
theorem single_step (t : F.advS.Domain) (qs : List (Tweak × M)) (tw : List Tweak)
    (c : Cache St Blk)
    {y : (F.advS.Range t × SM_DT_TCR_State Tweak M) × Cache St Blk}
    (hy : y ∈ support ((simulateQ chainRO ((tcrGameM F.single t).run (qs, tw))).run c)) :
    (¬ accepts F t (qs, tw) → y.1.2.1 = qs) ∧
      (accepts F t (qs, tw) → ∃ tm : Tweak × M, y.1.2.1 = qs ++ [tm] ∧ ∀ q ∈ qs, q.1 ≠ tm.1) := by
  rcases t with n | q | tm | q
  · rw [run_tcrGameM_inl, support_map] at hy
    obtain ⟨p, -, rfl⟩ := hy
    exact ⟨fun _ => rfl, fun h => absurd h (by simp [accepts])⟩
  · rw [run_tcrGameM_pub, support_map] at hy
    obtain ⟨p, -, rfl⟩ := hy
    exact ⟨fun _ => rfl, fun h => absurd h (by simp [accepts])⟩
  · rw [run_tcrGameM_chal] at hy
    split_ifs at hy with hcond
    · rw [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨fun _ => rfl, fun h => absurd hcond h⟩
    · rw [support_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      refine ⟨fun h => absurd hcond h, fun _ => ⟨tm, rfl, fun q hq he => ?_⟩⟩
      rw [not_or, not_not] at hcond
      exact hcond.2.1 ⟨q, hq, he⟩
  · rw [run_tcrGameM_coll] at hy
    split_ifs at hy with hcond
    · rw [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨fun _ => rfl, fun h => absurd h (by simp [accepts])⟩
    · rw [support_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      exact ⟨fun _ => rfl, fun h => absurd h (by simp [accepts])⟩

theorem mem_support_symD {t : F.advS.Domain} {p : SM_DT_TCR_State Tweak M × Cache St Blk}
    {z : F.advS.Range t × SM_DT_TCR_State Tweak M × Cache St Blk}
    (hz : z ∈ support ((symD F t).run p)) :
    ∃ y ∈ support ((simulateQ chainRO ((tcrGameM F.single t).run p.1)).run p.2),
      z = (y.1.1, (y.1.2, y.2)) := by
  simp only [symD, fuse, StateT.run_mk, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y, hy, rfl⟩

theorem mem_support_symE {L : ℕ} {t : F.advS.Domain}
    {S : (SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St)}
    {z : F.advS.Range t × (SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St)}
    (hz : z ∈ support ((symE F L t).run S)) :
    ∃ w ∈ support ((symD F t).run S.1), z.1 = w.1 ∧ z.2.1 = w.2 ∧
      ((¬ accepts F t S.1.1 ∧ z.2.2 = S.2) ∨
        (accepts F t S.1.1 ∧ ∃ h ∈ support (drawV (St := St) L), z.2.2 = S.2 ++ [h])) := by
  simp only [symE, StateT.run_mk] at hz
  split_ifs at hz with hacc
  · rw [mem_support_bind_iff] at hz
    obtain ⟨h, hh, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, rfl, rfl, .inr ⟨hacc, h, hh, rfl⟩⟩
  · rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, rfl, rfl, .inl ⟨hacc, rfl⟩⟩

/-- The eager symbolic game preserves the symbolic invariant. -/
theorem preservesInv_symE (L : ℕ) (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t) :
    QueryImpl.PreservesInv (symE F L) (fun S => SInv F btw L S.1.1 S.1.2 S.2) := by
  intro t S hS z hz
  obtain ⟨⟨⟨qs, tw⟩, c⟩, hs⟩ := S
  obtain ⟨w, hw, -, h2, h3⟩ := mem_support_symE hz
  obtain ⟨y, hy, rfl⟩ := mem_support_symD hw
  obtain ⟨a, ⟨s', c'⟩, hs'⟩ := z
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have htcr : TcrInv F.single btw y.1.2 y.2 :=
    tcrInv_step (F := F.single) btw hbtwT hbtwC t (qs, tw) c hS.tcr y hy
  obtain ⟨hna, hacc⟩ := single_step t qs tw c hy
  rcases h3 with ⟨hn, rfl⟩ | ⟨ha, h, hh, rfl⟩
  · have e := hna hn
    exact ⟨htcr, by rw [e]; exact hS.nodup, by rw [e]; exact hS.len, hS.lenL⟩
  · obtain ⟨tm, e, hfresh⟩ := hacc ha
    refine ⟨htcr, ?_, ?_, ?_⟩
    · show (y.1.2.1.map Prod.fst).Nodup
      rw [e, List.map_append, List.nodup_append]
      refine ⟨hS.nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      rw [hb]
      exact hfresh q hq
    · show (hs ++ [h]).length = y.1.2.1.length
      rw [e, List.length_append, List.length_append, hS.len]
      rfl
    · intro h' hh'
      rcases List.mem_append.mp hh' with h1 | h1
      · exact hS.lenL h' h1
      · rw [List.mem_singleton.mp h1]
        exact MB.length_of_mem_support_drawV L h hh

/-- Once the hidden values are not `Nice`, they stay so. -/
theorem preservesInv_not_nice (L : ℕ) :
    QueryImpl.PreservesInv (symE F L) (fun S => ¬ Nice (look S.1.2) S.2) := by
  intro t S hS z hz
  obtain ⟨⟨⟨qs, tw⟩, c⟩, hs⟩ := S
  obtain ⟨w, hw, -, h2, h3⟩ := mem_support_symE hz
  obtain ⟨y, hy, rfl⟩ := mem_support_symD hw
  obtain ⟨a, ⟨s', c'⟩, hs'⟩ := z
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have hle : CLe (look c) (look y.2) := CLe_of_le (chainRO_le _ c hy)
  intro hN
  rcases h3 with ⟨-, rfl⟩ | ⟨-, h, -, rfl⟩
  · exact hS (Nice_mono' hle hN)
  · exact hS (Nice_mono h hle hN)

theorem length_of_mem_support_symD {t : F.advS.Domain}
    {p : SM_DT_TCR_State Tweak M × Cache St Blk}
    {z : F.advS.Range t × SM_DT_TCR_State Tweak M × Cache St Blk}
    (hz : z ∈ support ((symD F t).run p)) :
    z.2.1.1.length = p.1.1.length + if accepts F t p.1 then 1 else 0 := by
  obtain ⟨⟨qs, tw⟩, c⟩ := p
  obtain ⟨y, hy, rfl⟩ := mem_support_symD hz
  obtain ⟨hna, hacc⟩ := single_step t qs tw c hy
  by_cases ha : accepts F t (qs, tw)
  · obtain ⟨tm, e, -⟩ := hacc ha
    simp only [ha, ↓reduceIte]
    show y.1.2.1.length = _
    rw [e, List.length_append]
    rfl
  · simp only [ha, ↓reduceIte]
    show y.1.2.1.length = _
    rw [hna ha]
    rfl

theorem isChal_of_accepts {t : F.advS.Domain} {s : SM_DT_TCR_State Tweak M}
    (h : accepts F t s) : F.isChal t = true := by
  rcases t with n | q | tm | q
  · exact absurd h (by simp [accepts])
  · exact absurd h (by simp [accepts])
  · rfl
  · exact absurd h (by simp [accepts])

/-! ## Deferring the hidden draws -/

/-- Drawing the hidden values after a step of the deferred game is drawing them before the step
of the eager game. -/
theorem intertwines_fillS (L : ℕ) :
    QueryImpl.IntertwinesOn (fun _ => True) (fillS (St := St) (Blk := Blk) (Tweak := Tweak)
      (M := M) L) (symD F) (symE F L) := by
  intro t p _ γ _ f
  have hlen := fun z hz => length_of_mem_support_symD (F := F) (t := t) (p := p) (z := z) hz
  by_cases hacc : accepts F t p.1
  · simp only [hacc, ↓reduceIte] at hlen
    calc 𝒟[(symD F t).run p >>= fun z => fillS L z.2 >>= f z.1]
        = 𝒟[(symD F t).run p >>= fun z => drawN (St := St) L p.1.1.length >>= fun hs =>
            drawV (St := St) L >>= fun h => f z.1 (z.2, hs ++ [h])] := by
          refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
          simp only [fillS, hlen z hz, drawN, bind_assoc, pure_bind, map_bind, map_pure]
      _ = 𝒟[drawN (St := St) L p.1.1.length >>= fun hs => (symD F t).run p >>= fun z =>
            drawV (St := St) L >>= fun h => f z.1 (z.2, hs ++ [h])] :=
          evalDist_bind_bind_swap_of_uniform _ _ _
      _ = 𝒟[drawN (St := St) L p.1.1.length >>= fun hs => drawV (St := St) L >>= fun h =>
            (symD F t).run p >>= fun z => f z.1 (z.2, hs ++ [h])] :=
          evalDist_bind_congr_of_support _ _ _ fun hs _ =>
            evalDist_bind_bind_swap_of_uniform _ _ _
      _ = _ := by
          simp only [fillS, symE, StateT.run_mk, hacc, ↓reduceIte, bind_assoc, bind_map_left]
  · simp only [hacc, ↓reduceIte, add_zero] at hlen
    calc 𝒟[(symD F t).run p >>= fun z => fillS L z.2 >>= f z.1]
        = 𝒟[(symD F t).run p >>= fun z => drawN (St := St) L p.1.1.length >>= fun hs =>
            f z.1 (z.2, hs)] := by
          refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
          simp only [fillS, hlen z hz, bind_map_left]
      _ = 𝒟[drawN (St := St) L p.1.1.length >>= fun hs => (symD F t).run p >>= fun z =>
            f z.1 (z.2, hs)] :=
          evalDist_bind_bind_swap_of_uniform _ _ _
      _ = _ := by
          simp only [fillS, symE, StateT.run_mk, hacc, ↓reduceIte, bind_map_left]

theorem mem_support_drawN (L n : ℕ) (hs : List (List St))
    (h : hs ∈ support (drawN (St := St) L n)) : hs.length = n ∧ ∀ x ∈ hs, x.length = L := by
  induction n generalizing hs with
  | zero =>
    simp only [drawN, support_pure, Set.mem_singleton_iff] at h
    subst h
    simp
  | succ n ih =>
    simp only [drawN, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨hs', h1, x, hx, rfl⟩ := h
    obtain ⟨e, hl⟩ := ih hs' h1
    refine ⟨by simp [e], fun y hy => ?_⟩
    rcases List.mem_append.mp hy with h2 | h2
    · exact hl y h2
    · rw [List.mem_singleton.mp h2]
      exact MB.length_of_mem_support_drawV L x hx

/-! ## The single-block cache -/

theorem CFin_of_enncard {c : Cache St Blk} {N : ℕ} (h : c.enncard ≤ N) : CFin (look c) N := by
  classical
  have h' : c.toSet.encard ≤ (N : ℕ∞) := by
    have : ((c.toSet.encard : ℕ∞) : ℝ≥0∞) ≤ ((N : ℕ∞) : ℝ≥0∞) := by
      rw [ENat.toENNReal_coe]; exact h
    exact ENat.toENNReal_le.mp this
  have hfin : c.toSet.Finite := Set.finite_of_encard_le_coe h'
  refine ⟨hfin.toFinset.toList.map Sigma.fst, ?_, fun x hx => ?_⟩
  · rw [List.length_map, Finset.length_toList]
    have := hfin.encard_eq_coe_toFinset_card
    rw [this] at h'
    exact_mod_cast h'
  · rw [List.mem_map]
    cases x with
    | inl q =>
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨⟨.inl q, u⟩, Finset.mem_toList.mpr (hfin.mem_toFinset.mpr hu), rfl⟩
    | inr B =>
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨⟨.inr B, u⟩, Finset.mem_toList.mpr (hfin.mem_toFinset.mpr hu), rfl⟩

theorem gd_update {IV : St} {κ : Cell St Blk → Option St} (x : Cell St Blk) {u : St}
    (hg : CInj κ ∧ ∀ y, κ y ≠ some IV) (hu : u ≠ IV) (hv : ∀ y, κ y ≠ some u) :
    CInj (Function.update κ x (some u)) ∧ ∀ y, Function.update κ x (some u) y ≠ some IV := by
  refine ⟨fun a b v ha hb => ?_, fun y => ?_⟩
  · by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · rw [hax, Function.update_self] at ha
      rw [Function.update_of_ne hbx] at hb
      exact absurd (ha ▸ hb) (hv b)
    · rw [hbx, Function.update_self] at hb
      rw [Function.update_of_ne hax] at ha
      exact absurd (hb ▸ ha) (hv a)
    · rw [Function.update_of_ne hax] at ha
      rw [Function.update_of_ne hbx] at hb
      exact hg.1 a b v ha hb
  · by_cases hyx : y = x
    · rw [hyx, Function.update_self]
      exact fun e => hu (Option.some.inj e)
    · rw [Function.update_of_ne hyx]
      exact hg.2 y

/-- A lazily sampled cache with at most `N` cells is injective without `IV` values except with
probability `N (N + 1) / |St|`. -/
theorem prEvent_flat_not_gd_le [Fintype St] (IV : St) {α : Type}
    (oa : OracleComp (unifSpec + (hS St Blk + tS St Blk)) α) (N : ℕ)
    (hq : IsQueryBoundP oa (fun i => i.isRight = true) N) :
    Pr{let z ← (simulateQ (hS St Blk + tS St Blk).romImpl oa).run ∅}[
        ¬ (CInj (look z.2) ∧ ∀ x, look z.2 x ≠ some IV)] ≤
      (N * (N + 1) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  haveI : Nonempty St := ⟨IV⟩
  have hcard : (Fintype.card St : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let P : Cache St Blk → Prop := fun c =>
    ¬ (CInj (look c) ∧ ∀ x, look c x ≠ some IV) ∧ c.enncard ≤ N
  have hP : ¬ P ∅ := fun h => h.1 ⟨fun x y v hx => by simp [look_empty] at hx,
    fun x => by simp [look_empty]⟩
  have hfresh : ∀ (t : (hS St Blk + tS St Blk).Domain) (c : Cache St Blk), ¬ P c → c t = none →
      Pr{let u ← ($ᵗ (hS St Blk + tS St Blk).Range t :
        ProbComp ((hS St Blk + tS St Blk).Range t))}[P (c.cacheQuery t u)] ≤
        ((N + 1 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
    intro t c hc ht
    by_cases hsz : c.enncard + 1 ≤ N
    · have hszc : c.enncard ≤ N := le_self_add.trans hsz
      have hG : CInj (look c) ∧ ∀ x, look c x ≠ some IV := by
        by_contra h
        exact hc ⟨h, hszc⟩
      obtain ⟨l, hl, hmem⟩ := CFin_of_enncard hszc
      have hbound : (((IV :: l.filterMap (look c)).length : ℕ) : ℝ≥0∞) *
          (Fintype.card St : ℝ≥0∞)⁻¹ ≤ ((N + 1 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
        refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
        have := List.length_filterMap_le (look c) l
        simp only [List.length_cons]
        omega
      have hgood : ∀ (x : Cell St Blk) (u : St), u ∉ IV :: l.filterMap (look c) →
          CInj (Function.update (look c) x (some u)) ∧
            ∀ y, Function.update (look c) x (some u) y ≠ some IV := by
        intro x u hu
        rw [List.mem_cons, not_or] at hu
        refine gd_update x hG hu.1 fun y hy => hu.2 ?_
        rw [List.mem_filterMap]
        exact ⟨y, hmem y (by rw [hy]; rfl), hy⟩
      rcases t with q | B
      · refine (prEvent_mono _ _ (fun u : St => u ∈ IV :: l.filterMap (look c)) fun u hu => ?_).trans
          ((MB.prEvent_uniform_mem_le _).trans hbound)
        by_contra hn
        apply hu.1
        rw [look_cacheQuery_inl]
        exact hgood _ u hn
      · refine (prEvent_mono _ _ (fun u : St => u ∈ IV :: l.filterMap (look c)) fun u hu => ?_).trans
          ((MB.prEvent_uniform_mem_le _).trans hbound)
        by_contra hn
        apply hu.1
        rw [look_cacheQuery_inr]
        exact hgood _ u hn
    · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => hsz (by
        rw [← QueryCache.enncard_cacheQuery c t u ht]; exact hu.2)]
      exact zero_le
  have key := OracleComp.prEvent_run_le_of_fresh_bound_of_isQueryBoundP
    (spec := hS St Blk + tS St Blk) P hP _ (ENNReal.mul_ne_top (by simp) hcard) hfresh oa hq
  refine (prEvent_mono_of_support _ _ _ fun z hz hz' => ?_).trans (key.trans (le_of_eq ?_))
  · exact ⟨hz', enncard_le_of_mem_support_run_unifFwdImpl_add_randomOracle hq hz⟩
  · push_cast
    ring

end

end MP1

/-- **Phase one.**  After phase one of the ideal game, the invariant `MInv` holds of the target
list and the joint cache, which has at most `q₁ + (qch + qc) (1 + Lc) + qch (L + 1)` cells,
except with probability `O(Q²)/|St|`; `hdom` is the domination of the real phase one by the
eager symbolic game. -/
theorem tcr_multi_phase1_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak]
    {F : THFam St Blk PkSeed Tweak M Y ι} (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hbtwC : ∀ i t m, btw (F.cch i t m).1 = t)
    (hdom : QueryImpl.DominatedUntilBad (symE F L) (conG F) (fbuild F)
      (fun S => SInv F btw L S.1.1 S.1.2 S.2) (fun S => ¬ Nice (look S.1.2) S.2))
    (A : TcrAdv F) (q₁ qch qc Lc : ℕ) (hq₁ : A.ChooseBound q₁) (hqch : A.ChalBound qch)
    (hqc : A.CollBound qc) (hLc : A.CollLen Lc) :
    Pr{let z ← (simulateQ (hS St Blk + tS St Blk).romImpl
        (simulateQ chainToT (tcrProg₁ A))).run ∅}[
      ¬ (MInv F btw L z.1.2.1 (look z.2) ∧
          CFin (look z.2) (q₁ + (qch + qc) * (1 + Lc) + qch * (L + 1)))] ≤
      ((q₁ + (qch + qc) * (1 + Lc)) * (q₁ + (qch + qc) * (1 + Lc) + 1) +
        (qch * L) * (qch * L + 2 * (q₁ + (qch + qc) * (1 + Lc)) + 1) : ℕ) *
          (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  generalize hN : q₁ + (qch + qc) * (1 + Lc) = N
  -- the single-block adversary and its flat program
  let A' : TcrAdv F.single := ⟨A.State, A.choose, A.forge⟩
  have hq₁' : A'.ChooseBound q₁ :=
    IsQueryBoundP.of_imp (p' := fun i => F.isH i = true)
      (fun t h => by rcases t with n | q | tm | q <;> exact h) hq₁
  have hqch' : A'.ChalBound qch :=
    IsQueryBoundP.of_imp (p' := fun i => F.isChal i = true)
      (fun t h => by rcases t with n | q | tm | q <;> exact h) hqch
  have hqc' : A'.CollBound qc :=
    IsQueryBoundP.of_imp (p' := fun i => F.isColl i = true)
      (fun t h => by rcases t with n | q | tm | q <;> exact h) hqc
  have hLc' : A'.CollLen Lc :=
    AllQueriesSatisfy.mono hLc (fun t h => by rcases t with n | q | tm | q <;> exact h)
  have hflat : IsQueryBoundP (simulateQ chainToT (tcrProg₁ A'))
      (fun i => Sum.isRight i = true) N := by
    rw [← hN]
    exact HP.isQueryBoundP_chainToT _ q₁ (qch + qc) Lc (tcrProg₁_pubBound A' hq₁')
      (tcrProg₁_chainBound A' hqch' hqc')
      (tcrProg₁_chainLen A' (fun _ _ => Nat.zero_le _) hLc')
  -- step 1: the real phase one is a run of `conG`
  have e1 : (simulateQ (hS St Blk + tS St Blk).romImpl (simulateQ chainToT (tcrProg₁ A))).run ∅ =
      (fun z => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (conG F) A.choose).run ((([] : List (Tweak × M)), ([] : List Tweak)), ∅) := by
    rw [simulateQ_romImpl_chainToT]
    exact MP1.fuse_run (tcrGameM F) A.choose ([], []) ∅
  rw [e1, prEvent_map]
  -- step 2: domination by the eager symbolic game
  have hf0 : fbuild F (((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)), []) =
      ((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)) := by
    simp [fbuild, build, entries, writeAll]
  have hS0 : SInv F btw L (([] : List (Tweak × M)), ([] : List Tweak)) (∅ : Cache St Blk) [] :=
    ⟨⟨by simp, by simp, fun B hB => by simp at hB, by simp⟩, by simp, rfl, by simp⟩
  have h2 := hdom.prEvent_simulateQ_run_le_map_or_bad (MP1.preservesInv_symE L btw hbtwT hbtwC)
    (MP1.preservesInv_not_nice L) A.choose
    (((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)), []) hS0
    (fun z => ¬ (MInv F btw L z.2.1.1 (look z.2.2) ∧ CFin (look z.2.2) (N + qch * (L + 1))))
  rw [hf0] at h2
  refine h2.trans ?_
  -- step 3: defer the hidden draws
  let E : (SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St) → Prop := fun S =>
    ¬ (MInv F btw L S.1.1.1 (build F (look S.1.2) S.1.1.1 S.2) ∧
        CFin (build F (look S.1.2) S.1.1.1 S.2) (N + qch * (L + 1))) ∨ ¬ Nice (look S.1.2) S.2
  have h3 := (MP1.intertwines_fillS (F := F) L).evalDist_simulateQ_run
    (fun _ _ _ _ _ => trivial) A.choose
    ((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)) trivial (γ := Bool)
    (fun _ S => (pure (decide (E S)) : ProbComp Bool))
  have hfill0 : fillS (St := St) (Blk := Blk) L
      ((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)) =
      pure (((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)), []) := by
    simp [fillS, drawN]
  rw [hfill0, pure_bind] at h3
  have e3 : Pr{let z ← ((simulateQ (symE F L) A.choose).run
        (((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)), []))}[
        ¬ (MInv F btw L (fbuild F z.2).1.1 (look (fbuild F z.2).2) ∧
          CFin (look (fbuild F z.2).2) (N + qch * (L + 1))) ∨ ¬ Nice (look z.2.1.2) z.2.2] =
      Pr{let S ← ((simulateQ (symD F) A.choose).run
          ((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)) >>=
            fun z => fillS L z.2)}[E S] := by
    have hE : ∀ z : A.State × (SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St),
        (¬ (MInv F btw L (fbuild F z.2).1.1 (look (fbuild F z.2).2) ∧
          CFin (look (fbuild F z.2).2) (N + qch * (L + 1))) ∨ ¬ Nice (look z.2.1.2) z.2.2) ↔
          E z.2 := fun z => by simp only [E, fbuild, look_ofLook]
    rw [prEvent_congr _ _ _ hE, prEvent_eq_evalDist_decide, prEvent_eq_evalDist_decide,
      bind_assoc]
    exact congrFun (congrArg DFunLike.coe h3.symm) {true}
  refine (le_of_eq e3).trans ?_
  -- step 4: the symbolic run in flat form
  set flatS := (simulateQ (hS St Blk + tS St Blk).romImpl
    (simulateQ chainToT (tcrProg₁ A'))).run ∅ with hflatS
  have e4 : (simulateQ (symD F) A.choose).run
      ((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk)) =
      (fun y => (y.1.1, (y.1.2, y.2))) <$> flatS := by
    rw [hflatS, simulateQ_romImpl_chainToT]
    exact MP1.run_fuse_eq (tcrGameM F.single) A.choose ([], []) ∅
  rw [e4, bind_map_left]
  have hgd := MP1.prEvent_flat_not_gd_le F.IV (simulateQ chainToT (tcrProg₁ A')) N hflat
  refine (prEvent_bind_le_prEvent_add_of_support flatS _
    (fun y => ¬ (CInj (look y.2) ∧ ∀ x, look y.2 x ≠ some F.IV)) E
    (ε := ((qch * L) * (qch * L + 2 * N + 1) : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹)
    fun y hy hG => ?_).trans ?_
  · rw [not_not] at hG
    -- deterministic facts of the symbolic run
    have hT : TcrInv F.single btw y.1.2 y.2 := tcrInv_phase1 (F := F.single) btw hbtwT hbtwC A' y hy
    have hnd : (y.1.2.1.map Prod.fst).Nodup := by
      refine chainRO_inv_of_step (tcrGameM F.single) (fun s _ => (s.1.map Prod.fst).Nodup)
        (fun t s c h z hz => ?_) A.choose ([], []) ∅ (by simp) y hy
      obtain ⟨qs, tw⟩ := s
      obtain ⟨hna, hacc⟩ := MP1.single_step (F := F) t qs tw c hz
      by_cases ha : accepts F t (qs, tw)
      · obtain ⟨tm, e, hfresh⟩ := hacc ha
        show (z.1.2.1.map Prod.fst).Nodup
        rw [e, List.map_append, List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro a ha' b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
        rw [hb]
        exact hfresh q hq
      · show (z.1.2.1.map Prod.fst).Nodup
        rw [hna ha]
        exact h
    have hfin : CFin (look y.2) N :=
      MP1.CFin_of_enncard (enncard_le_of_mem_support_run_unifFwdImpl_add_randomOracle hflat hy)
    have hlenq : y.1.2.1.length ≤ qch := by
      have hz' : (y.1.1, (y.1.2, y.2)) ∈ support ((simulateQ (symD F) A.choose).run
          ((([] : List (Tweak × M)), ([] : List Tweak)), (∅ : Cache St Blk))) := by
        rw [e4, support_map]
        exact ⟨y, hy, rfl⟩
      have := IsQueryBoundP.resource_le_add_of_mem_support_run_simulateQ
        (impl := symD F) (p := fun i => F.isChal i = true)
        (fun p : SM_DT_TCR_State Tweak M × Cache St Blk => (p.1.1.length : ℕ∞))
        (fun t s w hw => by
          rw [MP1.length_of_mem_support_symD hw]
          by_cases ha : accepts F t s.1
          · simp [ha, MP1.isChal_of_accepts ha]
          · simp only [ha, ↓reduceIte, add_zero, Nat.cast_le]
            exact le_self_add) hqch hz'
      simpa using this
    rw [fillS, prEvent_map]
    refine (prEvent_mono_of_support _ _ (fun hs => ¬ FillNice F.IV (look y.2) hs)
      fun hs hhs hE hFN => ?_).trans ((prEvent_drawN_not_fillNice F.IV (look y.2) N L _
        hfin).trans ?_)
    · obtain ⟨hl, hlL⟩ := MP1.mem_support_drawN L _ hs hhs
      have hS : SInv F btw L y.1.2 y.2 hs := ⟨hT, hnd, hl, hlL⟩
      obtain ⟨hM, hC⟩ := build_good L hlen btw hbtwT hS hG.1 hG.2 hFN hfin
      rcases hE with hE | hE
      · exact hE ⟨hM, MP1.CFin_mono hC (Nat.add_le_add_left
          (Nat.mul_le_mul_right _ hlenq) _)⟩
      · exact hE hFN.nice
    · refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
      have h1 : y.1.2.1.length * L ≤ qch * L := Nat.mul_le_mul_right L hlenq
      exact Nat.mul_le_mul h1 (Nat.add_le_add_right (Nat.add_le_add_right h1 _) _)
  · rw [Nat.cast_add, add_mul]
    exact add_le_add hgd le_rfl

end Ideal

#print axioms Ideal.tcr_multi_phase1_le
