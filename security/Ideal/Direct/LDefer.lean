import Ideal.Direct.LRelabel
import VCVio.OracleComp.QueryTracking.RandomOracle.Defer

/-!
# Deferred touches along a graph with non-injective points

A copy of the graph part of VCVio's `RandomOracle/Defer.lean` (Apache 2.0, A. Hicks) for the
graphs `LGraph` of `Direct/LRelabel.lean` (no `pt_inj`).  The state-level definitions
(`RelabelState.mask`, `revealCell`, `endFill`, `maskedFill`, `evalDist_drawCell_bind_maskedFill`)
are VCVio's and do not mention the graph.

* `eagerImpl`: the relabelled game with the label operations (`touch` draws and discards,
  `read` draws).
* `deferredImpl`: touches only recorded; `maskedImpl`: touched cells hidden until read.
* **`intertwines_maskedFill`**: exact, with no hypothesis on the points (both games choose the
  node at a point among the nodes with drawn children of the SAME state, so the same choice).
* **`dominatedUntilBad_maskedImpl`**: until `Bad = Conflict ∨ PtColl` (VCVio: until `Conflict`;
  the point collision is needed to identify the node the eager game draws).
* **`prEvent_eagerImpl_le_deferredImpl_empty`**: an event of the eager game is at most the same
  event of the deferred game after the end fill, or `Bad` of the filled state.
-/

open OracleComp OracleSpec

namespace Ideal.Direct

namespace LGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : LGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- The relabelled game extended by the label operations, each drawing its cell. -/
noncomputable def eagerImpl :
    QueryImpl (pub.withLabels X K R) (StateT (RelabelState pub X K R) ProbComp) :=
  G.relabelImpl +
    (RelabelState.labelImpl :
      QueryImpl (OracleSpec.labelOps X K R) (StateT (RelabelState pub X K R) ProbComp))

theorem eagerImpl_apply_inl (t : (pub.withDerivations X R).Domain) :
    G.eagerImpl (.inl t) = G.relabelImpl t := rfl

theorem eagerImpl_apply_inr (t : (OracleSpec.labelOps X K R).Domain) :
    G.eagerImpl (.inr t) = RelabelState.labelImpl t := rfl

theorem simulateQ_eagerImpl_liftComp {α : Type} (oa : OracleComp (pub.withDerivations X R) α) :
    simulateQ G.eagerImpl (liftComp oa (pub.withLabels X K R)) = simulateQ G.relabelImpl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, simulateQ_bind, ih]
    congr 1
    rcases t with (n | t) | x <;> rfl

/-- **The deferred game.** -/
noncomputable def deferredImpl : QueryImpl (pub.withLabels X K R)
    (StateT (RelabelState pub X K R × List (X ⊕ K)) ProbComp) := fun
  | .inl t => StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, s.2))) <$> (G.relabelImpl t).run s.1
  | .inr (.inl c) => StateT.mk fun s ↦ pure ((), (s.1, s.2 ++ [c]))
  | .inr (.inr k) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2))) <$> (RelabelState.drawCell (.inr k)).run s.1

open Classical in
/-- **The masked game.** -/
noncomputable def maskedImpl : QueryImpl (pub.withLabels X K R)
    (StateT (RelabelState pub X K R × Finset (X ⊕ K)) ProbComp) := fun
  | .inl (.inl (.inl n)) => StateT.mk fun s ↦ (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inl (.inr t)) => StateT.mk fun s ↦
      if h : ∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t then
        Prod.map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) id <$>
          (RelabelState.revealCell (.inr h.choose)).run s
      else (fun z ↦ (z.1, ((z.2, s.1.2), s.2))) <$> (pub.randomOracle t).run s.1.1
  | .inl (.inr x) => RelabelState.revealCell (.inl x)
  | .inr (.inl c) => StateT.mk fun s ↦
      (fun z ↦ ((), (z.2, if (s.1.2 c).isNone then insert c s.2 else s.2))) <$>
        (RelabelState.drawCell c).run s.1
  | .inr (.inr k) => RelabelState.revealCell (.inr k)

/-! ## Run equations -/

theorem deferredImpl_run_inl (t : (pub.withDerivations X R).Domain)
    (s : RelabelState pub X K R × List (X ⊕ K)) :
    (G.deferredImpl (.inl t)).run s = (fun z ↦ (z.1, (z.2, s.2))) <$> (G.relabelImpl t).run s.1 :=
  by simp only [deferredImpl, StateT.run_mk]

theorem deferredImpl_run_touch (c : X ⊕ K) (s : RelabelState pub X K R × List (X ⊕ K)) :
    (G.deferredImpl (.inr (.inl c))).run s = pure ((), (s.1, s.2 ++ [c])) := by
  simp only [deferredImpl, StateT.run_mk]

theorem deferredImpl_run_read (k : K) (s : RelabelState pub X K R × List (X ⊕ K)) :
    (G.deferredImpl (.inr (.inr k))).run s =
      (fun z ↦ (z.1, (z.2, s.2))) <$> (RelabelState.drawCell (.inr k)).run s.1 := by
  simp only [deferredImpl, StateT.run_mk]

theorem maskedImpl_run_unif (n : ℕ) (s : RelabelState pub X K R × Finset (X ⊕ K)) :
    (G.maskedImpl (.inl (.inl (.inl n)))).run s =
      (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp _) := by
  simp only [maskedImpl, StateT.run_mk]
  rfl

theorem maskedImpl_apply_derive (x : X) :
    G.maskedImpl (.inl (.inr x)) = RelabelState.revealCell (.inl x) := by
  simp only [maskedImpl]

theorem maskedImpl_apply_read (k : K) :
    G.maskedImpl (.inr (.inr k)) = RelabelState.revealCell (.inr k) := by
  simp only [maskedImpl]

theorem maskedImpl_run_touch (c : X ⊕ K) (s : RelabelState pub X K R × Finset (X ⊕ K)) :
    (G.maskedImpl (.inr (.inl c))).run s =
      (fun z ↦ ((), (z.2, if (s.1.2 c).isNone then insert c s.2 else s.2))) <$>
        (RelabelState.drawCell c).run s.1 := by
  simp only [maskedImpl, StateT.run_mk]

open Classical in
theorem maskedImpl_run_pub (t : ι) (s : RelabelState pub X K R × Finset (X ⊕ K)) :
    (G.maskedImpl (.inl (.inl (.inr t)))).run s =
      if h : ∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t then
        Prod.map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) id <$>
          (RelabelState.revealCell (.inr h.choose)).run s
      else (fun z ↦ (z.1, ((z.2, s.1.2), s.2))) <$> (pub.randomOracle t).run s.1.1 := by
  simp only [maskedImpl, StateT.run_mk]

theorem maskedImpl_run_pt {s : RelabelState pub X K R × Finset (X ⊕ K)}
    (hc : ¬ G.PtColl (RelabelState.mask s)) {k : K} {vs : List R}
    (h : G.childVals (RelabelState.mask s) k = some vs) :
    (G.maskedImpl (.inl (.inl (.inr (G.pt k vs))))).run s =
      Prod.map (cast (G.range_eq k vs).symm) id <$> (RelabelState.revealCell (.inr k)).run s := by
  rw [maskedImpl_run_pub]
  exact G.dite_exists_pt_eq hc h
    (fun k' e ↦ Prod.map (cast e.symm) id <$> (RelabelState.revealCell (.inr k')).run s) _

theorem maskedImpl_run_pub_of_not_exists {s : RelabelState pub X K R × Finset (X ⊕ K)} {t : ι}
    (ht : ¬∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t) :
    (G.maskedImpl (.inl (.inl (.inr t)))).run s =
      (fun z ↦ (z.1, ((z.2, s.1.2), s.2))) <$> (pub.randomOracle t).run s.1.1 := by
  rw [maskedImpl_run_pub]
  simp only [ht, ↓reduceDIte]

/-! ## The masked end fill intertwines the deferred and masked games -/

/-- The masked end fill intertwines the deferred game with the masked game (no hypothesis on
the points: both games choose among the nodes of the same state). -/
theorem intertwines_maskedFill :
    QueryImpl.Intertwines RelabelState.maskedFill G.deferredImpl G.maskedImpl := by
  classical
  rintro (((n | t) | x) | (c | k)) ⟨st, cs⟩ γ _ f
  · rw [deferredImpl_run_inl, relabelImpl_run_unif]
    simp only [maskedImpl_run_unif, bind_map_left]
    exact OracleComp.evalDist_bind_bind_swap _ _ fun u s' ↦ f u s'
  · by_cases h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
    · rw [deferredImpl_run_inl, relabelImpl_run_pub]
      simp only [h, ↓reduceDIte, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq]
      refine (RelabelState.evalDist_drawCell_bind_maskedFill (.inr h.choose) st cs
        fun u s' ↦ f (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm u) s').trans ?_
      refine evalDist_bind_congr_of_support _ _ _ fun s' hs' ↦ ?_
      have hm := RelabelState.mask_eq_of_mem_support_maskedFill hs'
      subst hm
      rw [maskedImpl_run_pub]
      simp only [h, ↓reduceDIte, bind_map_left]
      rfl
    · rw [deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists h]
      set F := (simulateQ ((X ⊕ K) →ₒ R).randomOracle (((X ⊕ K) →ₒ R).queryAll cs)).run st.2
      calc _ = 𝒟[(pub.randomOracle t).run st.1 >>= fun y ↦ F >>= fun w ↦
            f y.1 ((y.2, w.2), st.2.uncached cs)] := by
            simp only [Functor.map_map, bind_map_left, RelabelState.maskedFill_eq, F]
        _ = 𝒟[F >>= fun w ↦ (pub.randomOracle t).run st.1 >>= fun y ↦
            f y.1 ((y.2, w.2), st.2.uncached cs)] := OracleComp.evalDist_bind_bind_swap _ _ _
        _ = _ := by
          rw [RelabelState.maskedFill_eq, bind_map_left]
          refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
          have hm := RelabelState.mask_eq_of_mem_support_maskedFill (st := st) (cs := cs)
            (s' := ((st.1, w.2), st.2.uncached cs))
            (by rw [RelabelState.maskedFill_eq, support_map]; exact ⟨w, hw, rfl⟩)
          rw [G.maskedImpl_run_pub_of_not_exists (by rw [hm]; exact h), bind_map_left]
  · rw [deferredImpl_run_inl, relabelImpl_apply_inr, bind_map_left, maskedImpl_apply_derive]
    exact RelabelState.evalDist_drawCell_bind_maskedFill (.inl x) st cs f
  · rw [deferredImpl_run_touch, pure_bind, RelabelState.maskedFill_eq, RelabelState.maskedFill_eq,
      OracleSpec.queryAll_append, simulateQ_bind, StateT.run_bind]
    simp only [bind_map_left, map_bind, maskedImpl_run_touch, RelabelState.drawCell_run,
      OracleSpec.queryAll_cons, OracleSpec.queryAll_nil, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
    refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
    rw [QueryImpl.withCaching_queryAll_uncached_append_singleton _ hw c]
  · rw [deferredImpl_run_read, bind_map_left, maskedImpl_apply_read]
    exact RelabelState.evalDist_drawCell_bind_maskedFill (.inr k) st cs f

/-! ## Monotonicity -/

theorem le_of_mem_support_deferredImpl {t : (pub.withLabels X K R).Domain}
    {s : RelabelState pub X K R × List (X ⊕ K)} {z}
    (hz : z ∈ support ((G.deferredImpl t).run s)) : s.1 ≤ z.2.1 := by
  rcases t with t | c | k
  · rw [deferredImpl_run_inl, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact G.le_of_mem_support_relabelImpl hw
  · rw [deferredImpl_run_touch, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ le_rfl
  · rw [deferredImpl_run_read, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1

theorem le_of_mem_support_maskedImpl {t : (pub.withLabels X K R).Domain}
    {s : RelabelState pub X K R × Finset (X ⊕ K)} {z} (hz : z ∈ support ((G.maskedImpl t).run s)) :
    s.1 ≤ z.2.1 := by
  classical
  rcases t with ((n | t) | x) | (c | k)
  · rw [maskedImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact le_rfl
  · rw [maskedImpl_run_pub] at hz
    split_ifs at hz with ht
    · rw [RelabelState.revealCell_run, Functor.map_map, support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
    · rw [support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨QueryImpl.withCaching_cache_le _ _ _ _ hw, le_rfl⟩
  · rw [maskedImpl_apply_derive, RelabelState.revealCell_run, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
  · rw [maskedImpl_run_touch, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
  · rw [maskedImpl_apply_read, RelabelState.revealCell_run, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1

theorem preservesInv_bad_maskedImpl :
    QueryImpl.PreservesInv G.maskedImpl fun s ↦ G.Bad s.1 :=
  fun _ _ h _ hz ↦ h.mono G (G.le_of_mem_support_maskedImpl hz)

/-! ## The masked game is dominated by the eager game until `Bad` -/

theorem dominatedUntilBad_maskedImpl :
    QueryImpl.DominatedUntilBad G.maskedImpl G.eagerImpl Prod.fst (fun _ ↦ True)
      fun s ↦ G.Bad s.1 := by
  intro t s _ hb Q
  have hp : ¬ G.PtColl s.1 := fun h ↦ hb (Or.inr h)
  have hpm : ¬ G.PtColl (RelabelState.mask s) := fun h ↦ hp (h.mono G (RelabelState.mask_le s))
  have key (h : Prod.map id Prod.fst <$> (G.maskedImpl t).run s = (G.eagerImpl t).run s.1) :
      Pr{let z ← (G.maskedImpl t).run s}[Q (z.1, z.2.1) ∧ ¬G.Bad z.2.1] ≤
        Pr{let z ← (G.eagerImpl t).run s.1}[Q z] := by
    rw [← h, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h ↦ h.1
  rcases t with ((n | t) | x) | (c | k)
  · refine key ?_
    rw [maskedImpl_run_unif, eagerImpl_apply_inl, relabelImpl_run_unif, Functor.map_map]
    rfl
  · by_cases hr : ∃ k vs, G.childVals (RelabelState.mask s) k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := hr
      refine key ?_
      rw [G.maskedImpl_run_pt hpm hk, eagerImpl_apply_inl,
        G.relabelImpl_run_pt hp (G.childVals_mono (RelabelState.mask_le s) hk),
        RelabelState.revealCell_run, Functor.map_map, Functor.map_map]
      rfl
    · by_cases hf : ∃ k vs, G.childVals s.1 k = some vs ∧ G.pt k vs = t
      · obtain ⟨k, vs, hk, rfl⟩ := hf
        refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 ?_)
          zero_le
        rw [G.maskedImpl_run_pub_of_not_exists hr, support_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact Or.inl ⟨k, vs, G.childVals_mono (st := s.1) (st' := (w.2, s.1.2))
          ⟨QueryImpl.withCaching_cache_le _ _ _ _ hw, le_rfl⟩ hk,
          by rw [QueryImpl.withCaching_run_caches _ _ _ _ hw]; rfl⟩
      · refine key ?_
        rw [G.maskedImpl_run_pub_of_not_exists hr, eagerImpl_apply_inl,
          G.relabelImpl_run_pub_of_not_exists hf, Functor.map_map]
        rfl
  · refine key ?_
    rw [maskedImpl_apply_derive, RelabelState.revealCell_run, eagerImpl_apply_inl,
      relabelImpl_apply_inr, Functor.map_map]
    simp only [Prod.map_apply, id_eq, Prod.mk.eta, id_map']
  · refine key ?_
    rw [maskedImpl_run_touch, eagerImpl_apply_inr, Functor.map_map]
    simp only [Prod.map_apply, id_eq, RelabelState.labelImpl, StateT.run_map]
  · refine key ?_
    rw [maskedImpl_apply_read, RelabelState.revealCell_run, eagerImpl_apply_inr,
      Functor.map_map]
    simp only [Prod.map_apply, id_eq, Prod.mk.eta, id_map', RelabelState.labelImpl]

/-! ## Deferring touches -/

theorem prEvent_deferredImpl_endFill_eq_maskedFill_bind_maskedImpl {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) (s : RelabelState pub X K R × List (X ⊕ K))
    (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.deferredImpl oa).run s
       let st ← RelabelState.endFill z.2}[P (z.1, st)] =
      Pr{let s' ← RelabelState.maskedFill s
         let z ← (simulateQ G.maskedImpl oa).run s'}[P (z.1, z.2.1)] := by
  have h := G.intertwines_maskedFill.evalDist_simulateQ_run oa s
    fun a s' ↦ (pure (P (a, s'.1)) : ProbComp Prop)
  simp only [RelabelState.maskedFill, bind_map_left, prEvent_norm] at h ⊢
  rw [prEvent_def, prEvent_def, h]

theorem prEvent_deferredImpl_endFill_eq_maskedImpl {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) (st : RelabelState pub X K R)
    (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.deferredImpl oa).run (st, [])
       let st' ← RelabelState.endFill z.2}[P (z.1, st')] =
      Pr{let z ← (simulateQ G.maskedImpl oa).run (st, ∅)}[P (z.1, z.2.1)] := by
  rw [prEvent_deferredImpl_endFill_eq_maskedFill_bind_maskedImpl, RelabelState.maskedFill_nil,
    pure_bind]

theorem prEvent_eagerImpl_le_maskedImpl {α : Type} (oa : OracleComp (pub.withLabels X K R) α)
    (s : RelabelState pub X K R × Finset (X ⊕ K)) (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.eagerImpl oa).run s.1}[P z] ≤
      Pr{let z ← (simulateQ G.maskedImpl oa).run s}[P (z.1, z.2.1) ∨ G.Bad z.2.1] :=
  G.dominatedUntilBad_maskedImpl.prEvent_simulateQ_run_le_map_or_bad
    (QueryImpl.PreservesInv.trivial _) G.preservesInv_bad_maskedImpl oa s trivial P

/-- **Touch deferral (non-injective points).** -/
theorem prEvent_eagerImpl_le_deferredImpl {α : Type} (oa : OracleComp (pub.withLabels X K R) α)
    (st : RelabelState pub X K R) (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.eagerImpl oa).run st}[P z] ≤
      Pr{let z ← (simulateQ G.deferredImpl oa).run (st, [])
         let st' ← RelabelState.endFill z.2}[P (z.1, st') ∨ G.Bad st'] :=
  (G.prEvent_eagerImpl_le_maskedImpl oa (st, ∅) P).trans_eq
    (G.prEvent_deferredImpl_endFill_eq_maskedImpl oa st fun z ↦ P z ∨ G.Bad z.2).symm

theorem prEvent_eagerImpl_le_deferredImpl_empty {α : Type}
    (oa : OracleComp (pub.withLabels X K R) α) (P : α × RelabelState pub X K R → Prop) :
    Pr{let z ← (simulateQ G.eagerImpl oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.deferredImpl oa).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[P (z.1, st) ∨ G.Bad st] :=
  G.prEvent_eagerImpl_le_deferredImpl oa (∅, ∅) P

end LGraph

end Ideal.Direct

#print axioms Ideal.Direct.LGraph.intertwines_maskedFill
#print axioms Ideal.Direct.LGraph.dominatedUntilBad_maskedImpl
#print axioms Ideal.Direct.LGraph.prEvent_eagerImpl_le_deferredImpl_empty
