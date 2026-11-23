import Ideal.Direct.CoupleUnif

/-!
# Run equations of one step of both games (`status/DIRECT.md` §14)

Normal forms for the domination of the coupling:

* **D side** (`defH k`): an honest walk touches its proper prefixes (only recorded) and draws
  its full node (`walk_def`); so a `Thash`/PRF step reads one node, a two-stage step two
  (`defH_hon`); a forger cell is the relabelled oracle (`defH_port`).
* **R side** (`romGE k`): an honest step is the oracle at `u` and two eager ghost draws
  (`romGE_hon`); a forger cell is the simulator step with eager ghost reads (`romGE_port`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-! ## Walks in the deferred game -/

/-- The node a walk from the reversed prefix `rev` reads. -/
def nodeR : List Blk → List Blk → MD.Nd Blk
  | rev, [] => (default, rev)
  | rev, [b] => (b, rev)
  | rev, b :: b' :: bs => nodeR (b :: rev) (b' :: bs)

/-- The touches of a walk from `rev`. -/
def tch : List Blk → List Blk → List (Empty ⊕ MD.Nd Blk)
  | _, [] => []
  | _, [_] => []
  | rev, b :: b' :: bs => .inr (b, rev) :: tch (b :: rev) (b' :: bs)

/-- **A walk in the deferred game**: the touches are recorded, the full node is drawn. -/
theorem walk_def : ∀ (bs : List Blk), bs ≠ [] → ∀ (rev : List Blk) (st : MD.RS St Blk)
    (P : List (Empty ⊕ MD.Nd Blk)),
    (simulateQ Gs.deferredImpl (MD.walkL IV128 rev bs)).run (st, P) =
      (fun z => (z.1, (z.2, P ++ tch rev bs))) <$>
        (RelabelState.drawCell (.inr (nodeR rev bs))).run st
  | [], h, _, _, _ => absurd rfl h
  | [b], _, rev, st, P => by
    simp only [MD.walkL, MD.rL, simulateQ_spec_query, nodeR, tch, List.append_nil]
    rw [LGraph.deferredImpl_run_read]
  | b :: b' :: bs, _, rev, st, P => by
    simp only [MD.walkL, MD.tL, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [LGraph.deferredImpl_run_touch, pure_bind]
    show (simulateQ Gs.deferredImpl (MD.walkL IV128 (b :: rev) (b' :: bs))).run
      (st, P ++ [.inr (b, rev)]) = _
    refine (walk_def (b' :: bs) (List.cons_ne_nil _ _) (b :: rev) st (P ++ [.inr (b, rev)])).trans ?_
    simp only [nodeR, tch, List.append_assoc, List.singleton_append]

theorem nodeR_eq : ∀ (bs : List Blk), bs ≠ [] → ∀ rev, nodeR rev bs =
    (bs.getLastD default, bs.dropLast.reverse ++ rev)
  | [], h, _ => absurd rfl h
  | [b], _, rev => by simp [nodeR]
  | b :: b' :: bs, _, rev => by
    rw [nodeR, nodeR_eq (b' :: bs) (List.cons_ne_nil _ _)]
    simp

theorem nodeR_nil (bs : List Blk) (h : bs ≠ []) : nodeR [] bs = ndOf bs := by
  rw [nodeR_eq bs h]; simp [ndOf]

/-! ## One step of `defH` -/

theorem defH_apply (k : Bytes 16) (t : (QT Dsk).Domain) :
    defH k t = simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128)
      (simulateQ (chainW k) (untagT t))) := rfl

theorem defH_coin (k : Bytes 16) (n : ℕ) (d : DS) :
    (defH k (.inl n)).run d = (fun u => (u, d)) <$> (unifSpec.query n : ProbComp _) := by
  rw [defH_apply]
  simp only [untagT, simulateQ_spec_query, chainW, MD.labI]
  rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_unif, Functor.map_map]

theorem defH_port (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (d : DS) :
    (defH k (.inr (.inl (.inl (pk, q))))).run d =
      (fun z => (z.1, (z.2, d.2))) <$> (Gs.relabelImpl (.inl (.inr q))).run d.1 := by
  rw [defH_apply]
  simp only [untagT, portQ, simulateQ_spec_query, chainW, MD.labI, MD.cL]
  rw [LGraph.deferredImpl_run_inl]

theorem labI_wQ (bs : List Blk) :
    simulateQ (MD.labI IV128) (wQ bs) = MD.walkL IV128 [] bs := by
  unfold wQ; rw [simulateQ_spec_query]; rfl

/-- A one-walk step of `defH`. -/
theorem defH_walk1 {β : Type} (f : St → β) (bs : List Blk) (hbs : bs ≠ []) (d : DS) :
    (simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128) (f <$> wQ bs))).run d =
      (fun z => (f z.1, (z.2, d.2 ++ tch [] bs))) <$>
        (RelabelState.drawCell (.inr (ndOf bs))).run d.1 := by
  rw [simulateQ_map, simulateQ_map, labI_wQ, StateT.run_map, walk_def bs hbs, nodeR_nil bs hbs,
    Functor.map_map]

theorem tw_ne (ps : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2 ≠ [] := List.cons_ne_nil _ _

/-- **A `Thash` step of `defH`**: its final node is drawn. -/
theorem defH_thash (k : Bytes 16) (ps : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) (d : DS) :
    (defH k (.inr (.inr (.inl (.thash ps a xs))))).run d =
      (fun z => ((out16 z.1, (z.2, d.2 ++ tch [] (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2))) :
        (QT Dsk).Range (.inr (.inr (.inl (.thash ps a xs)))) × DS)) <$>
        (RelabelState.drawCell (.inr (ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2)))).run d.1 := by
  rw [defH_apply]
  simp only [untagT, simulateQ_spec_query, chainW, hashPW, hashW]
  exact defH_walk1 out16 _ (tw_ne ps a xs) d

/-- **A PRF step of `defH`.** -/
theorem defH_prf (k : Bytes 16) (dd : Dsk) (d : DS) :
    (defH k (.inr (.inl (.inr dd)))).run d =
      (fun z => ((out16 z.1, (z.2, d.2 ++ tch [] [sb128 dd.1, blk128 dd.2 k])) :
        (QT Dsk).Range (.inr (.inl (.inr dd))) × DS)) <$>
        (RelabelState.drawCell (.inr (ndOf [sb128 dd.1, blk128 dd.2 k]))).run d.1 := by
  rw [defH_apply]
  simp only [untagT, simulateQ_spec_query, chainW]
  exact defH_walk1 out16 _ (List.cons_ne_nil _ _) d

/-- A two-walk step of `defH`. -/
theorem defH_walk2 {β : Type} (f : St → β) (bs : List Blk) (g : St → List Blk) (hbs : bs ≠ [])
    (hg : ∀ s, g s ≠ []) (d : DS) :
    (simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128)
      (wQ bs >>= fun s => wQ (g s) >>= fun s' => pure (f s')))).run d =
      (RelabelState.drawCell (.inr (ndOf bs))).run d.1 >>= fun z₁ =>
        (fun z₂ => (f z₂.1, (z₂.2, d.2 ++ tch [] bs ++ tch [] (g z₁.1)))) <$>
          (RelabelState.drawCell (.inr (ndOf (g z₁.1)))).run z₁.2 := by
  simp only [simulateQ_bind, simulateQ_pure, labI_wQ, StateT.run_bind]
  rw [walk_def bs hbs, nodeR_nil bs hbs, bind_map_left]
  refine bind_congr fun z₁ => ?_
  rw [walk_def (g z₁.1) (hg _), nodeR_nil _ (hg _), bind_map_left]
  simp only [StateT.run_pure, map_eq_bind_pure_comp]
  rfl

theorem iblocksH_ne (R ps pr : Bytes 16) (M : List UInt8) : iblocksH R ps pr M ≠ [] := by
  intro h; have := iblocksH_length R ps pr M; rw [h] at this; simp at this

theorem oblocksH_ne (R ps : Bytes 16) (s : St) : oblocksH R ps s ≠ [] := by
  intro h; have := oblocksH_length R ps s; rw [h] at this; simp at this

/-- **An `H_msg` step of `defH`**: the inner node, then the outer node at the inner label. -/
theorem defH_hmsg (k : Bytes 16) (R ps pr : Bytes 16) (M : List UInt8) (d : DS) :
    (defH k (.inr (.inr (.inl (.hmsg R ps pr M))))).run d =
      (RelabelState.drawCell (.inr (ndOf (iblocksH R ps pr M)))).run d.1 >>= fun z₁ =>
        (fun z₂ => ((dig30 z₂.1, (z₂.2, d.2 ++ tch [] (iblocksH R ps pr M) ++
            tch [] (oblocksH R ps z₁.1))) : (QT Dsk).Range (.inr (.inr (.inl (.hmsg R ps pr M)))) × DS)) <$>
          (RelabelState.drawCell (.inr (ndOf (oblocksH R ps z₁.1)))).run z₁.2 := by
  rw [defH_apply]
  simp only [untagT, simulateQ_spec_query, chainW, hashPW, hashW]
  exact defH_walk2 dig30 _ _ (iblocksH_ne R ps pr M) (oblocksH_ne R ps) d

/-- **A `PRF_msg` step of `defH`.** -/
theorem defH_prfmsg (k : Bytes 16) (k' o : Bytes 16) (M : List UInt8) (d : DS) :
    (defH k (.inr (.inr (.inr (k', o, M))))).run d =
      (RelabelState.drawCell (.inr (ndOf (ikey k' :: iblocks o M)))).run d.1 >>= fun z₁ =>
        (fun z₂ => ((out16 z₂.1, (z₂.2, d.2 ++ tch [] (ikey k' :: iblocks o M) ++
            tch [] [okey k', oblock z₁.1])) : (QT Dsk).Range (.inr (.inr (.inr (k', o, M)))) × DS)) <$>
          (RelabelState.drawCell (.inr (ndOf [okey k', oblock z₁.1]))).run z₁.2 := by
  rw [defH_apply]
  simp only [untagT, simulateQ_spec_query, chainW, hashPW, prfW]
  exact defH_walk2 out16 _ _ (List.cons_ne_nil _ _) (fun _ => List.cons_ne_nil _ _) d

/-! ## One step of `romGE` -/

theorem eG_o (t : (hashSpec Cr).Domain) (G : GS) :
    (simulateQ gG.eagerImpl (oG t)).run G =
      (fun z => (z.1, (z.2, G.2))) <$> (PubG.randomOracle (.inl t)).run G.1 := by
  unfold oG
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inl,
    LGraph.relabelImpl_run_pub_of_not_exists _ (gG_no_pt t G)]

theorem eG_t (c : KG) (G : GS) :
    (simulateQ gG.eagerImpl (tG c)).run G =
      (fun z => ((), z.2)) <$> (RelabelState.drawCell (.inr c)).run G := by
  unfold tG
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inr]
  simp [RelabelState.labelImpl]

theorem eG_r (c : KG) (G : GS) :
    (simulateQ gG.eagerImpl (rG c)).run G = (RelabelState.drawCell (.inr c)).run G := by
  unfold rG
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inr]
  rfl

theorem eG_coin (n : ℕ) (G : GS) :
    (simulateQ gG.eagerImpl (coinG n)).run G =
      (fun u => (u, G)) <$> (unifSpec.query n : ProbComp _) := by
  unfold coinG
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inl, LGraph.relabelImpl_run_unif]

theorem eG_fresh (G : GS) :
    (simulateQ gG.eagerImpl freshG).run G = (fun u => (u, G)) <$> ($ᵗ St : ProbComp St) := by
  unfold freshG
  rw [← QueryImpl.simulateQ_compose]
  refine (run_simulateQ_statelessP _ (fun n => (liftM (unifSpec.query n) : ProbComp _))
    (fun n s' => ?_) _ G).trans ?_
  · simp only [QueryImpl.apply_compose]
    exact eG_coin n s'
  · rw [simulateQ_unif_id]

theorem eG_hon (u : (hashSpec Cr).Domain) (G : GS) :
    (simulateQ gG.eagerImpl (honG u)).run G =
      (PubG.randomOracle (.inl u)).run G.1 >>= fun z =>
        (RelabelState.drawCell (.inr (u, false))).run (z.2, G.2) >>= fun w₁ =>
          (fun w₂ => (z.1, w₂.2)) <$> (RelabelState.drawCell (.inr (u, true))).run w₁.2 := by
  unfold honG
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, eG_o, eG_t, bind_map_left,
    StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  rfl

/-- The ghost draw, in distribution: a fresh value is drawn and used only if the ghost is
undrawn. -/
theorem drawCell_eqD (c : KG) (G : GS) :
    (RelabelState.drawCell (.inr c)).run G =ᵈ
      (($ᵗ St : ProbComp St) >>= fun g => pure ((G.2 (.inr c)).getD g, (G.1, gset G.2 c g))) := by
  cases h : G.2 (.inr c) with
  | some g₀ =>
    rw [RelabelState.drawCell_run_of_cell_eq_some h]
    simp only [Option.getD_some, gset, h]
    exact (EvalDistEq.bind_const _ _).symm
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none h]
    simp only [Option.getD_none, gset, h, map_eq_bind_pure_comp]
    exact EvalDistEq.refl _

/-- The cached-or-fresh oracle answer of the R side. -/
noncomputable def RY (u : (hashSpec Cr).Domain) (C : PubG.QueryCache) :
    ProbComp ((hashSpec Cr).Range u) :=
  match C (.inl u) with
  | some y => pure y
  | none => ($ᵗ ((hashSpec Cr).Range u) : ProbComp _)

/-- Cache the answer if uncached. -/
def cset (u : (hashSpec Cr).Domain) (C : PubG.QueryCache) (y : (hashSpec Cr).Range u) :
    PubG.QueryCache :=
  match C (.inl u) with
  | none => C.cacheQuery (.inl u) y
  | some _ => C

theorem ro_eqD (u : (hashSpec Cr).Domain) (C : PubG.QueryCache) :
    (PubG.randomOracle (.inl u)).run C =ᵈ (RY u C >>= fun y => pure (y, cset u C y)) := by
  rw [randomOracle.run_eq]
  cases h : C (.inl u) with
  | some y => simp only [RY, cset, h, pure_bind]; exact EvalDistEq.refl _
  | none =>
    simp only [RY, cset, h]
    exact EvalDistEq.of_forall_prEvent_eq fun p => by
      simp only [prEvent_norm]
      exact SampleableType.prEvent_uniformSample_inst_irrel _ _ _

/-- **An honest step of `romGE`, in distribution**: the oracle answer (cached or fresh) and two
ghost draws used only if undrawn. -/
theorem romGE_hon_eqD (u : (hashSpec Cr).Domain) (T : Tc) (C : PubG.QueryCache) (G : GLT) :
    (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ gG.eagerImpl ((liftT (honG u)).run T)).run ((C, G) : GS) =ᵈ
      (RY u C >>= fun y => ($ᵗ St : ProbComp St) >>= fun g₁ => ($ᵗ St : ProbComp St) >>= fun g₂ =>
        pure (y, (T, (cset u C y, gset (gset G (u, false) g₁) (u, true) g₂)))) := by
  rw [liftT_run, simulateQ_map, StateT.run_map, eG_hon]
  simp only [map_bind, Functor.map_map, map_pure]
  refine (EvalDistEq.bind_left (ro_eqD u C) _).trans ?_
  rw [bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun y _ => ?_
  rw [pure_bind]
  refine (EvalDistEq.bind_left (drawCell_eqD (u, false) (cset u C y, G)) _).trans ?_
  rw [bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun g₁ _ => ?_
  rw [pure_bind]
  refine (EvalDistEq.map (drawCell_eqD (u, true) (cset u C y, gset G (u, false) g₁)) _).trans ?_
  simp only [map_bind, map_pure]
  exact EvalDistEq.refl _

end Ideal.Direct.Rom
