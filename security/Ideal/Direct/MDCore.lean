import Ideal.Direct.LDefer
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# The Merkle–Damgård relabel/deferral core (H2, first part; `status/DIRECT.md` §11)

Generic in the chaining-value type `St`, the block type `Blk` and the initial value `IV`.

* The **program interface** `OSp St Blk = unifSpec + Cell + WSp`: coins, compression queries
  `Cell = (St × Blk →ₒ St)` (the forger's port) and **walk queries** `WSp = (List Blk →ₒ St)`: an
  honest Merkle–Damgård evaluation of a block list from `IV`, answered by its full final
  chaining value.  Every honest hash of SLH-DSA-SHA2 (`Thash`, the two stages of `H_msg`, the two
  HMAC stages of `PRF_msg`, the secret-key `PRF`) is a program over walk queries (the second
  stage's block list is computed from the first stage's answer), so one generic statement covers
  all of them.
* The **real game**: compression queries and walk queries answered in ONE lazy table (`romImpl`),
  a walk by the chain of its compression queries (`cellsR`, `walkR`).
* The graph `mdG IV`: nodes `(b, rev)` = the block list `reverse rev ++ [b]`, parent `rev`, point
  `(label of the parent or IV, b)` (`LGraph`, non-injective points).
* The **deferred game**: VCVio-style relabelled game on `mdG IV` where a walk is the label
  operations `touch` (every proper prefix) and `read` (the full list) (`labI`, `walkL`), with the
  touches deferred (`LGraph.deferredImpl`) and drawn at the end (`RelabelState.endFill`).

**Theorem (`md_core`).**  For every program `X` over `OSp` and every event `P` of its output,
```
Pr_real[P] ≤ Pr_deferred[P] + 3 · Pr_deferred;endFill[Bad]
```
with `Bad = Conflict ∨ PtColl` of `mdG IV` at the filled final state (a label equal to the
chaining input of a cached non-node cell, two drawn nodes with the same cell: 256-bit events).
The proof: real = VCVio's `SecretEncoding.idealImpl` (`real_eq_ideal`); relabelling
(`LGraph.prEvent_idealImpl_le_relabelImpl`); the relabelled run of the compression chains is the
eager run of the same program with walks as label operations until a point collision
(`walk_agree`, `AgreeUntilBad`); touch deferral (`LGraph.prEvent_eagerImpl_le_deferredImpl_empty`).
-/

open OracleComp OracleSpec

set_option linter.unusedSectionVars false

namespace Ideal.Direct.MD

section Specs

variable (St Blk : Type)

/-- Compression queries. -/
abbrev Cell : OracleSpec (St × Blk) := (St × Blk) →ₒ St

/-- Merkle–Damgård nodes: `(b, rev)` is the block list `rev.reverse ++ [b]`. -/
abbrev Nd : Type := Blk × List Blk

/-- Walk queries: an honest evaluation of a block list, answered by its final chaining value. -/
abbrev WSp : OracleSpec (List Blk) := List Blk →ₒ St

/-- The program interface: coins, compression queries, walk queries. -/
abbrev OSp := unifSpec + Cell St Blk + WSp St Blk

/-- VCVio's interface with (no) derivations. -/
abbrev W := (Cell St Blk).withDerivations Empty St

/-- VCVio's interface with label operations on the Merkle–Damgård nodes. -/
abbrev WL := (Cell St Blk).withLabels Empty (Nd Blk) St

end Specs

variable {St Blk : Type}

/-- Children of a node: its parent, if any. -/
def mdCh : Nd Blk → List (Empty ⊕ Nd Blk)
  | (_, []) => []
  | (_, p :: ps) => [.inr (p, ps)]

/-- **The Merkle–Damgård graph.** -/
def mdG (IV : St) : LGraph (Cell St Blk) Empty (Nd Blk) St where
  ch := mdCh
  pt k vs := (vs.headD IV, k.1)
  range_eq _ _ := rfl
  root_inj := by
    rintro ⟨b, ps⟩ ⟨b', ps'⟩ h h' hpt
    cases ps with
    | cons p ps => simp [mdCh] at h
    | nil =>
      cases ps' with
      | cons p ps => simp [mdCh] at h'
      | nil =>
        simp only [List.headD_nil, Prod.mk.injEq, true_and] at hpt
        subst hpt; rfl

/-! ## Walks -/

section Walks

variable (IV : St)

/-- A compression query of the real interface. -/
def cR (q : St × Blk) : OracleComp (unifSpec + Cell St Blk) St :=
  (liftM ((unifSpec + Cell St Blk).query (.inr q)) : OracleComp (unifSpec + Cell St Blk) St)

/-- A compression query of the label interface. -/
def cL (q : St × Blk) : OracleComp (WL St Blk) St :=
  (liftM ((WL St Blk).query (.inl (.inl (.inr q)))) : OracleComp (WL St Blk) St)

/-- A touch of a node. -/
def tL (k : Nd Blk) : OracleComp (WL St Blk) Unit :=
  (liftM ((WL St Blk).query (.inr (.inl (.inr k)))) : OracleComp (WL St Blk) Unit)

/-- A read of a node. -/
def rL (k : Nd Blk) : OracleComp (WL St Blk) St :=
  (liftM ((WL St Blk).query (.inr (.inr k))) : OracleComp (WL St Blk) St)

/-- The chain of compression queries of a block list from the chaining value `c` (real). -/
def walkR : St → List Blk → OracleComp (unifSpec + Cell St Blk) St
  | c, [] => pure c
  | c, b :: bs => cR (c, b) >>= fun v => walkR v bs

/-- The same chain over the label interface. -/
def walkC : St → List Blk → OracleComp (WL St Blk) St
  | c, [] => pure c
  | c, b :: bs => cL (c, b) >>= fun v => walkC v bs

/-- The walk as label operations: touch every proper prefix node, read the full one.  `rev` is
the reversed list of the blocks already walked. -/
def walkL : List Blk → List Blk → OracleComp (WL St Blk) St
  | _, [] => pure IV
  | rev, [b] => rL (b, rev)
  | rev, b :: b' :: bs => tL (b, rev) >>= fun _ => walkL (b :: rev) (b' :: bs)

/-- **Real interpretation**: walks by compression chains. -/
def cellsR : QueryImpl (OSp St Blk) (OracleComp (unifSpec + Cell St Blk))
  | .inl t => (liftM ((unifSpec + Cell St Blk).query t) : OracleComp (unifSpec + Cell St Blk) _)
  | .inr bs => walkR IV bs

/-- The real interpretation over the label interface (no label operation). -/
def cellsL : QueryImpl (OSp St Blk) (OracleComp (WL St Blk))
  | .inl (.inl n) => (liftM ((WL St Blk).query (.inl (.inl (.inl n)))) : OracleComp (WL St Blk) _)
  | .inl (.inr q) => cL (q)
  | .inr bs => walkC IV bs

/-- **Label interpretation**: walks by label operations. -/
def labI : QueryImpl (OSp St Blk) (OracleComp (WL St Blk))
  | .inl (.inl n) => (liftM ((WL St Blk).query (.inl (.inl (.inl n)))) : OracleComp (WL St Blk) _)
  | .inl (.inr q) => cL (q)
  | .inr bs => walkL IV [] bs

end Walks

/-! ## Probability helper -/

theorem prEvent_bind_congr_supp {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[p y] = Pr{let y ← g a}[q y]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let y ← mx >>= g}[q y] :=
  le_antisymm (prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun a ha ↦ (h a ha).le)
    (prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun a ha ↦ (h a ha).ge)

/-! ## The eager game along a walk -/

section Eager

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] (IV : St)

/-- The relabelled state of the Merkle–Damgård graph. -/
abbrev RS (St Blk : Type) := RelabelState (Cell St Blk) Empty (Nd Blk) St

/-- The parent condition of a walk position: no parent and `c = IV`, or the parent drawn at
`c`. -/
def PC (st : RS St Blk) : List Blk → St → Prop
  | [], c => c = IV
  | p :: ps, c => st.2 (.inr (p, ps)) = some c

theorem childVals_pc {st : RS St Blk} {rev : List Blk} {c : St} (h : PC IV st rev c) (b : Blk) :
    ∃ vs, (mdG (Blk := Blk) IV).childVals st (b, rev) = some vs ∧ (mdG (Blk := Blk) IV).pt (b, rev) vs = (c, b) := by
  cases rev with
  | nil =>
    refine ⟨[], (mdG (Blk := Blk) IV).childVals_of_ch_nil rfl, ?_⟩
    simp only [PC] at h
    subst h; rfl
  | cons p ps =>
    refine ⟨[c], ?_, rfl⟩
    simp only [PC] at h
    simp [LGraph.childVals, mdG, mdCh, h]

theorem le_of_mem_support_eagerImpl {t : (WL St Blk).Domain} {st : RS St Blk} {z}
    (hz : z ∈ support (((mdG (Blk := Blk) IV).eagerImpl t).run st)) : st ≤ z.2 := by
  rcases t with t | t
  · exact (mdG (Blk := Blk) IV).le_of_mem_support_relabelImpl hz
  · exact RelabelState.le_of_mem_support_labelImpl (pub := Cell St Blk) (X := Empty) (K := Nd Blk) (R := St) hz

theorem preservesInv_bad_eager : QueryImpl.PreservesInv (mdG (Blk := Blk) IV).eagerImpl (mdG (Blk := Blk) IV).Bad :=
  fun _ _ h _ hz ↦ h.mono _ (le_of_mem_support_eagerImpl IV hz)

theorem eager_cL {st : RS St Blk} (hp : ¬ (mdG (Blk := Blk) IV).PtColl st) {rev : List Blk} {c : St}
    (h : PC IV st rev c) (b : Blk) :
    (simulateQ (mdG (Blk := Blk) IV).eagerImpl (cL (c, b))).run st =
      (RelabelState.drawCell (.inr (b, rev))).run st := by
  obtain ⟨vs, hk, hpt⟩ := childVals_pc IV h b
  unfold cL
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inl]
  rw [← hpt, (mdG (Blk := Blk) IV).relabelImpl_run_pt hp hk]
  have e : (Prod.map (cast ((mdG (Blk := Blk) IV).range_eq (b, rev) vs).symm) id :
      St × RS St Blk → St × RS St Blk) = id := by
    funext x; rfl
  rw [e, id_map]

theorem eager_tL (k : Nd Blk) (st : RS St Blk) :
    (simulateQ (mdG (Blk := Blk) IV).eagerImpl (tL k)).run st =
      (fun z ↦ ((), z.2)) <$> (RelabelState.drawCell (.inr k)).run st := by
  unfold tL
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inr]
  simp [RelabelState.labelImpl]

theorem eager_rL (k : Nd Blk) (st : RS St Blk) :
    (simulateQ (mdG (Blk := Blk) IV).eagerImpl (rL k)).run st = (RelabelState.drawCell (.inr k)).run st := by
  unfold rL
  rw [simulateQ_spec_query, LGraph.eagerImpl_apply_inr]
  rfl

theorem prEvent_bad_run_zero {α : Type} (oa : OracleComp (WL St Blk) α) {st : RS St Blk}
    (hb : (mdG (Blk := Blk) IV).Bad st) (Q : α × RS St Blk → Prop) :
    Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).eagerImpl oa).run st}[Q z ∧ ¬ (mdG (Blk := Blk) IV).Bad z.2] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2
    (simulateQ_run_preservesInv _ _ (preservesInv_bad_eager IV) oa st hb z hz)

/-- **A walk by compression queries is its label operations, until a point collision.** -/
theorem walk_agree : ∀ (bs : List Blk), bs ≠ [] → ∀ (rev : List Blk) (c : St) (st : RS St Blk),
    ¬ (mdG (Blk := Blk) IV).Bad st → PC IV st rev c → ∀ Q : St × RS St Blk → Prop,
    Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).eagerImpl (walkC c bs)).run st}[Q z ∧ ¬ (mdG (Blk := Blk) IV).Bad z.2] =
      Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).eagerImpl (walkL IV rev bs)).run st}[
        Q z ∧ ¬ (mdG (Blk := Blk) IV).Bad z.2]
  | [], h, _, _, _, _, _, _ => absurd rfl h
  | [b], _, rev, c, st, hb, hpc, Q => by
    have hp : ¬ (mdG (Blk := Blk) IV).PtColl st := fun h ↦ hb (Or.inr h)
    simp only [walkC.eq_2, walkC.eq_1, walkL.eq_2, bind_pure, eager_cL IV hp hpc, eager_rL]
  | b :: b' :: bs, _, rev, c, st, hb, hpc, Q => by
    have hp : ¬ (mdG (Blk := Blk) IV).PtColl st := fun h ↦ hb (Or.inr h)
    rw [walkC.eq_2, walkL.eq_3]
    simp only [simulateQ_bind, StateT.run_bind, eager_cL IV hp hpc, eager_tL,
      bind_map_left]
    refine prEvent_bind_congr_supp _ _ _ _ _ fun z hz ↦ ?_
    by_cases hbz : (mdG (Blk := Blk) IV).Bad z.2
    · rw [prEvent_bad_run_zero IV _ hbz, prEvent_bad_run_zero IV _ hbz]
    · exact walk_agree (b' :: bs) (List.cons_ne_nil _ _) (b :: rev) z.1 z.2 hbz
        (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).2 Q

/-- The real interpretation, run in the eager game. -/
noncomputable abbrev implA : QueryImpl (OSp St Blk) (StateT (RS St Blk) ProbComp) :=
  (mdG (Blk := Blk) IV).eagerImpl ∘ₛ cellsL IV

/-- The label interpretation, run in the eager game. -/
noncomputable abbrev implB : QueryImpl (OSp St Blk) (StateT (RS St Blk) ProbComp) :=
  (mdG (Blk := Blk) IV).eagerImpl ∘ₛ labI IV

theorem agree_AB : QueryImpl.AgreeUntilBad (implA IV) (implB IV) (mdG (Blk := Blk) IV).Bad := by
  rintro ((n | q) | bs) st hb Q
  · rfl
  · rfl
  · cases bs with
    | nil => rfl
    | cons b bs =>
      exact walk_agree IV (b :: bs) (List.cons_ne_nil _ _) [] IV st hb rfl Q

theorem preservesInv_bad_B : QueryImpl.PreservesInv (implB IV) (mdG (Blk := Blk) IV).Bad :=
  fun _ s hs z hz ↦ simulateQ_run_preservesInv _ _ (preservesInv_bad_eager IV) _ s hs z hz

end Eager

/-! ## The real game is VCVio's ideal (lazy) game with no derivations -/

section Real

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

theorem real_eq_ideal {α : Type} (Y : OracleComp (unifSpec + Cell St Blk) α)
    (C : (Cell St Blk).QueryCache) (D : (Empty →ₒ St).QueryCache) :
    (simulateQ (SecretEncoding.idealImpl (Cell St Blk) Empty St)
        (simulateQ ((Cell St Blk).withDerivationsLift Empty St) Y)).run (C, D) =
      (fun z ↦ (z.1, (z.2, D))) <$> (simulateQ (Cell St Blk).romImpl Y).run C := by
  induction Y using OracleComp.inductionOn generalizing C with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | q
    · simp only [OracleSpec.withDerivationsLift, simulateQ_spec_query]
      simp [SecretEncoding.idealImpl, ih, unifFwdImpl, bind_pure_comp]
    · simp only [OracleSpec.withDerivationsLift, simulateQ_spec_query]
      simp [SecretEncoding.idealImpl, ih]

end Real

/-! ## The core -/

section Core

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] (IV : St)

theorem walk_lift : ∀ (c : St) (bs : List Blk),
    simulateQ (mdG (Blk := Blk) IV).relabelImpl
        (simulateQ ((Cell St Blk).withDerivationsLift Empty St) (walkR c bs)) =
      simulateQ (mdG (Blk := Blk) IV).eagerImpl (walkC c bs)
  | c, [] => by simp [walkR, walkC]
  | c, b :: bs => by
    simp only [walkR, walkC, simulateQ_bind, cR, cL, simulateQ_spec_query,
      OracleSpec.withDerivationsLift, LGraph.eagerImpl_apply_inl]
    exact bind_congr fun v ↦ walk_lift v bs

theorem lift_eq {α : Type} (X : OracleComp (OSp St Blk) α) :
    simulateQ (mdG (Blk := Blk) IV).relabelImpl
        (simulateQ ((Cell St Blk).withDerivationsLift Empty St) (simulateQ (cellsR IV) X)) =
      simulateQ (implA IV) X := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with (n | q) | bs
  · simp [cellsR, cellsL, OracleSpec.withDerivationsLift, LGraph.eagerImpl_apply_inl]
  · simp [cellsR, cellsL, cL, OracleSpec.withDerivationsLift, LGraph.eagerImpl_apply_inl]
  · simp only [QueryImpl.apply_compose, cellsR, cellsL]
    rw [QueryImpl.simulateQ_compose]
    exact walk_lift IV IV bs

/-- **The Merkle–Damgård relabel/deferral core.**  For every program over coins, compression
queries and walk queries, and every event of its output: the real game (one lazy table, walks
by compression chains) is at most the deferred game (walks as label operations with their
touches deferred) plus twice the probability of `Bad` at the filled final state. -/
theorem md_core {α : Type} (X : OracleComp (OSp St Blk) α) (P : α → Prop) :
    Pr{let z ← (simulateQ (Cell St Blk).romImpl (simulateQ (cellsR IV) X)).run' ∅}[P z] ≤
      Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
         let _st ← RelabelState.endFill z.2}[P z.1] + 2 *
      Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[(mdG (Blk := Blk) IV).Bad st] := by
  set G := mdG (Blk := Blk) IV
  set Y := simulateQ (cellsR IV) X
  -- real = VCVio's ideal game
  have h1 : Pr{let z ← (simulateQ (Cell St Blk).romImpl Y).run' ∅}[P z] =
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Cell St Blk) Empty St)
        (simulateQ ((Cell St Blk).withDerivationsLift Empty St) Y)).run (∅, ∅)}[P z.1] := by
    rw [real_eq_ideal, prEvent_map, StateT.run', prEvent_map]
    rfl
  -- relabelling
  have h2 := G.prEvent_idealImpl_le_relabelImpl
    (simulateQ ((Cell St Blk).withDerivationsLift Empty St) Y) (fun z ↦ P z.1)
  rw [lift_eq] at h2
  -- walks as label operations
  have h3 := (agree_AB IV).prEvent_simulateQ_run_le_add_bad_right (preservesInv_bad_B IV) X
    (∅, ∅) (fun z ↦ P z.1 ∨ G.Bad z.2)
  have hB : simulateQ (implB IV) X = simulateQ G.eagerImpl (simulateQ (labI IV) X) :=
    QueryImpl.simulateQ_compose _ _ _
  rw [hB] at h3
  -- deferral
  have h4 := G.prEvent_eagerImpl_le_deferredImpl_empty (simulateQ (labI IV) X)
    (fun z ↦ P z.1 ∨ G.Bad z.2)
  have h5 := G.prEvent_eagerImpl_le_deferredImpl_empty (simulateQ (labI IV) X)
    (fun z ↦ G.Bad z.2)
  set A := (simulateQ G.deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
  set D : ProbComp (α × RS St Blk) := A >>= fun z ↦ RelabelState.endFill z.2 >>= fun st ↦
    pure (z.1, st) with hD
  have conv : ∀ E : α → RS St Blk → Prop,
      Pr{let z ← A; let st ← RelabelState.endFill z.2}[E z.1 st] = Pr{let w ← D}[E w.1 w.2] := by
    intro E
    rw [hD]
    simp only [prEvent_norm]
  rw [conv (fun a _ ↦ P a), conv (fun _ st ↦ G.Bad st)]
  rw [conv (fun a st ↦ (P a ∨ G.Bad st) ∨ G.Bad st)] at h4
  rw [conv (fun _ st ↦ G.Bad st ∨ G.Bad st)] at h5
  have h6 : Pr{let w ← D}[(P w.1 ∨ G.Bad w.2) ∨ G.Bad w.2] ≤
      Pr{let w ← D}[P w.1] + Pr{let w ← D}[G.Bad w.2] :=
    (prEvent_mono _ _ _ fun w hw ↦ by tauto).trans (prEvent_or_le _ _ _)
  have h7 : Pr{let w ← D}[G.Bad w.2 ∨ G.Bad w.2] = Pr{let w ← D}[G.Bad w.2] :=
    prEvent_congr _ _ _ fun w ↦ or_self_iff
  have hP : ∀ z : α × RS St Blk, (P (z.1, G.toSplitCache z.2).1 ∨ G.Bad z.2) ↔ (P z.1 ∨ G.Bad z.2) :=
    fun _ ↦ Iff.rfl
  calc _ = _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ (Pr{let w ← D}[P w.1] + Pr{let w ← D}[G.Bad w.2]) + Pr{let w ← D}[G.Bad w.2] :=
      add_le_add (h4.trans h6) (h5.trans h7.le)
    _ = _ := by rw [two_mul, add_assoc]

end Core

/-! ## What `Bad` means for Merkle–Damgård -/

section BadMeaning

variable (IV : St)

theorem childVals_inv {st : RS St Blk} {k : Nd Blk} {vs : List St}
    (h : (mdG (Blk := Blk) IV).childVals st k = some vs) :
    (k.2 = [] ∧ vs = []) ∨ ∃ p ps v, k.2 = p :: ps ∧ vs = [v] ∧ st.2 (.inr (p, ps)) = some v := by
  obtain ⟨b, rev⟩ := k
  cases rev with
  | nil =>
    left
    refine ⟨rfl, ?_⟩
    have := (mdG (Blk := Blk) IV).childVals_of_ch_nil (st := st) (k := (b, [])) rfl
    rw [this] at h
    exact (Option.some_inj.1 h).symm
  | cons p ps =>
    right
    have h2 := (mdG (Blk := Blk) IV).childVals_eq_some_iff.1 h
    simp only [mdG, mdCh] at h2
    obtain ⟨v, vs', hv, hnil, rfl⟩ := List.forall₂_cons_left_iff.1 h2
    obtain rfl := List.forall₂_nil_left_iff.1 hnil
    exact ⟨p, ps, v, rfl, rfl, hv⟩

/-- **A point collision of the Merkle–Damgård graph is a label collision or a label equal to
`IV`**: two distinct drawn nodes with the same label, or a drawn node labelled `IV`. -/
theorem ptColl_imp {st : RS St Blk} (h : (mdG (Blk := Blk) IV).PtColl st) :
    (∃ k k' v, k ≠ k' ∧ st.2 (.inr k) = some v ∧ st.2 (.inr k') = some v) ∨
      ∃ k, st.2 (.inr k) = some IV := by
  obtain ⟨⟨b, rev⟩, ⟨b', rev'⟩, vs, vs', hk, hk', hpt, hne⟩ := h
  rcases childVals_inv IV hk with ⟨h1, rfl⟩ | ⟨p, ps, v, h1, rfl, hv⟩ <;>
    rcases childVals_inv IV hk' with ⟨h2, rfl⟩ | ⟨p', ps', v', h2, rfl, hv'⟩
  · exact absurd ((mdG (Blk := Blk) IV).root_inj (by simp only at h1; simp [mdG, mdCh, h1])
      (by simp only at h2; simp [mdG, mdCh, h2]) hpt) hne
  · simp only [mdG, List.headD_nil, List.headD_cons, Prod.mk.injEq] at hpt
    exact Or.inr ⟨(p', ps'), hpt.1 ▸ hv'⟩
  · simp only [mdG, List.headD_nil, List.headD_cons, Prod.mk.injEq] at hpt
    exact Or.inr ⟨(p, ps), hpt.1 ▸ hv⟩
  · simp only [mdG, List.headD_cons, Prod.mk.injEq] at hpt
    obtain ⟨rfl, rfl⟩ := hpt
    simp only at h1 h2
    subst h1 h2
    by_cases hpp : (p, ps) = (p', ps')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpp
      exact absurd rfl hne
    · exact Or.inl ⟨(p, ps), (p', ps'), v, hpp, hv, hv'⟩

/-- **A conflict of the Merkle–Damgård graph is a drawn label equal to the chaining input of a
cached non-node cell** (or a cached root cell `(IV, b)`). -/
theorem conflict_imp {st : RS St Blk} (h : (mdG (Blk := Blk) IV).Conflict st) :
    (∃ k v b, st.2 (.inr k) = some v ∧ (st.1 (v, b)).isSome) ∨ ∃ b, (st.1 (IV, b)).isSome := by
  obtain ⟨⟨b, rev⟩, vs, hk, hc⟩ := h
  rcases childVals_inv IV hk with ⟨-, rfl⟩ | ⟨p, ps, v, -, rfl, hv⟩
  · exact Or.inr ⟨b, hc⟩
  · exact Or.inl ⟨(p, ps), v, b, hv, hc⟩

end BadMeaning

end Ideal.Direct.MD

#print axioms Ideal.Direct.MD.walk_agree
#print axioms Ideal.Direct.MD.real_eq_ideal
#print axioms Ideal.Direct.MD.md_core
#print axioms Ideal.Direct.MD.ptColl_imp
#print axioms Ideal.Direct.MD.conflict_imp
