import Ideal.Direct.CoupleRun

/-!
# Domination of the joint handler at an honest query (`status/DIRECT.md` §13.4 step 3, §14)

The core inequality (`core1`): the D draw of the final label `v` of an honest query (fresh iff
`fv`), the splice `splice u h v` for the ghost tail and an independent `h'`, restricted to the
steps the joint handler does not flag, are dominated by the R side's
`y ← (O(u) cached or fresh); g ← $; g' ← $`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal SampleableType

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-- The flag of an honest step. -/
def flagH (C : PubG.QueryCache) (u : (hashSpec Cr).Domain) (fv : Prop) (v : St) : Prop :=
  match C (.inl u) with
  | none => ¬ fv
  | some y => y ≠ ansOf u v

theorem prEvent_eq_conj_le {α β : Type} (mx : ProbComp α) (my : ProbComp β) (y : α)
    (P : α → β → Prop) :
    Pr{let y' ← mx; let z ← my}[P y' z ∧ y = y'] ≤ Pr{let z ← my}[P y z] := by
  calc Pr{let y' ← mx; let z ← my}[P y' z ∧ y = y']
      ≤ Pr{let y' ← mx; let z ← my}[P y z] :=
        prEvent_bind_mono_of_support _ _ _ fun y' _ => prEvent_mono _ _ _
          fun z h => h.2 ▸ h.1
    _ = Pr{let z ← my}[P y z] := OracleComp.prEvent_bind_const _ _

/-- Splitting under an independent third draw. -/
theorem splice_unif3 (u : (hashSpec Cr).Domain) (Q : (hashSpec Cr).Range u → St → St → Prop) :
    Pr{let v ← ($ᵗ St : ProbComp St)
       let h ← ($ᵗ St : ProbComp St)
       let h' ← ($ᵗ St : ProbComp St)}[Q (ansOf u v) (splice u h v) h'] =
      Pr{let y ← ($ᵗ ((hashSpec Cr).Range u) : ProbComp _)
         let g ← ($ᵗ St : ProbComp St)
         let h' ← ($ᵗ St : ProbComp St)}[Q y g h'] := by
  calc _ = Pr{let v ← ($ᵗ St : ProbComp St)
              let h' ← ($ᵗ St : ProbComp St)
              let h ← ($ᵗ St : ProbComp St)}[Q (ansOf u v) (splice u h v) h'] :=
        prEvent_bind_congr_of_support _ _ _ fun v _ => prEvent_bind_map_swap _ _ _
    _ = Pr{let h' ← ($ᵗ St : ProbComp St)
           let v ← ($ᵗ St : ProbComp St)
           let h ← ($ᵗ St : ProbComp St)}[Q (ansOf u v) (splice u h v) h'] :=
        prEvent_bind_bind_swap _ _ _
    _ = Pr{let h' ← ($ᵗ St : ProbComp St)
           let y ← ($ᵗ ((hashSpec Cr).Range u) : ProbComp _)
           let g ← ($ᵗ St : ProbComp St)}[Q y g h'] :=
        prEvent_bind_congr_of_support _ _ _ fun h' _ =>
          splice_unif u (fun p => Q p.1 p.2 h')
    _ = Pr{let y ← ($ᵗ ((hashSpec Cr).Range u) : ProbComp _)
           let h' ← ($ᵗ St : ProbComp St)
           let g ← ($ᵗ St : ProbComp St)}[Q y g h'] :=
        prEvent_bind_bind_swap _ _ _
    _ = _ := prEvent_bind_congr_of_support _ _ _ fun y _ => prEvent_bind_map_swap _ _ _

/-- **The core inequality of an honest step** (one draw of the final label). -/
theorem core1 (u : (hashSpec Cr).Domain) (C : PubG.QueryCache) (n : MD.Nd Blk)
    (st : MD.RS St Blk) (fv : Prop) [Decidable fv] (hfv : fv ↔ st.2 (.inr n) = none)
    (Q : (hashSpec Cr).Range u → St → St → Prop) :
    Pr{let z ← (RelabelState.drawCell (.inr n)).run st
       let h ← ($ᵗ St : ProbComp St)
       let h' ← ($ᵗ St : ProbComp St)}[
        Q (ansOf u z.1) (if fv then splice u h z.1 else h) h' ∧ ¬ flagH C u fv z.1] ≤
      Pr{let y ← RY u C
         let g ← ($ᵗ St : ProbComp St)
         let h' ← ($ᵗ St : ProbComp St)}[Q y g h'] := by
  cases hn : st.2 (.inr n) with
  | some w =>
    have hf : ¬ fv := fun h => by rw [hfv, hn] at h; cases h
    rw [RelabelState.drawCell_run_of_cell_eq_some hn, pure_bind]
    simp only [hf, ↓reduceIte]
    cases hC : C (.inl u) with
    | none =>
      simp only [flagH, hC, hf, not_false_eq_true, not_true_eq_false, and_false]
      refine le_of_eq_of_le ?_ zero_le
      rw [OracleComp.prEvent_bind_const]
      exact (prEvent_eq_zero_iff _ _).2 fun _ _ h => h
    | some y =>
      simp only [flagH, hC, RY, pure_bind, ne_eq, not_not]
      refine prEvent_bind_mono_of_support _ _ _ fun g _ => prEvent_mono _ _ _ fun h' h => ?_
      obtain ⟨h1, h2⟩ := h
      rw [h2]; exact h1
  | none =>
    have hf : fv := hfv.2 hn
    rw [RelabelState.drawCell_run_of_cell_eq_none hn, bind_map_left]
    simp only [hf, ↓reduceIte]
    cases hC : C (.inl u) with
    | none =>
      simp only [flagH, hC, hf, not_true_eq_false, not_false_eq_true, and_true, RY]
      exact (splice_unif3 u Q).le
    | some y =>
      simp only [flagH, hC, RY, pure_bind, ne_eq, not_not]
      rw [splice_unif3 u (fun y' g h' => Q y' g h' ∧ y = y')]
      calc _ ≤ Pr{let y' ← ($ᵗ ((hashSpec Cr).Range u) : ProbComp _)
                  let g ← ($ᵗ St : ProbComp St)
                  let h' ← ($ᵗ St : ProbComp St)}[Q y g h'] :=
            prEvent_bind_mono_of_support _ _ _ fun y' _ => prEvent_bind_mono_of_support _ _ _
              fun g _ => prEvent_mono _ _ _ fun h' h => by
                obtain ⟨h1, h2⟩ := h; subst h2; exact h1
        _ = _ := OracleComp.prEvent_bind_const _ _

theorem drawCell_support_cells {n : MD.Nd Blk} {st : MD.RS St Blk} {z : St × MD.RS St Blk}
    (hz : z ∈ support ((RelabelState.drawCell (.inr n)).run st)) (c : Empty ⊕ MD.Nd Blk)
    (hc : c ≠ .inr n) : z.2.2 c = st.2 c := by
  cases hn : st.2 (.inr n) with
  | some w =>
    rw [RelabelState.drawCell_run_of_cell_eq_some hn, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none hn, support_map] at hz
    obtain ⟨v, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_of_ne _ _ hc

/-- **The core inequality of a two-stage honest step** (inner label, then the final label of
the outer walk at it). -/
theorem core2 (u : (hashSpec Cr).Domain) (C : PubG.QueryCache) (m : MD.Nd Blk)
    (nO : St → MD.Nd Blk) (st : MD.RS St Blk) (Q : (hashSpec Cr).Range u → St → St → Prop) :
    Pr{let z₁ ← (RelabelState.drawCell (.inr m)).run st
       let z₂ ← (RelabelState.drawCell (.inr (nO z₁.1))).run z₁.2
       let h ← ($ᵗ St : ProbComp St)
       let h' ← ($ᵗ St : ProbComp St)}[
        Q (ansOf u z₂.1)
          (if st.2 (.inr (nO z₁.1)) = none ∧ m ≠ nO z₁.1 then splice u h z₂.1 else h)
          (if st.2 (.inr m) = none then z₁.1 else h') ∧
        ¬ flagH C u (st.2 (.inr (nO z₁.1)) = none ∧ m ≠ nO z₁.1) z₂.1] ≤
      Pr{let y ← RY u C
         let g ← ($ᵗ St : ProbComp St)
         let g' ← ($ᵗ St : ProbComp St)}[Q y g g'] := by
  -- the final draw, for each inner draw, by `core1`
  have step1 :
      Pr{let z₁ ← (RelabelState.drawCell (.inr m)).run st
         let z₂ ← (RelabelState.drawCell (.inr (nO z₁.1))).run z₁.2
         let h ← ($ᵗ St : ProbComp St)
         let h' ← ($ᵗ St : ProbComp St)}[
          Q (ansOf u z₂.1)
            (if st.2 (.inr (nO z₁.1)) = none ∧ m ≠ nO z₁.1 then splice u h z₂.1 else h)
            (if st.2 (.inr m) = none then z₁.1 else h') ∧
          ¬ flagH C u (st.2 (.inr (nO z₁.1)) = none ∧ m ≠ nO z₁.1) z₂.1] ≤
      Pr{let z₁ ← (RelabelState.drawCell (.inr m)).run st
         let y ← RY u C
         let g ← ($ᵗ St : ProbComp St)
         let h' ← ($ᵗ St : ProbComp St)}[Q y g (if st.2 (.inr m) = none then z₁.1 else h')] := by
    refine prEvent_bind_mono_of_support _ _ _ fun z₁ hz₁ => ?_
    have hm := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz₁).2
    refine core1 u C (nO z₁.1) z₁.2 (st.2 (.inr (nO z₁.1)) = none ∧ m ≠ nO z₁.1) ?_
      (fun y g h' => Q y g (if st.2 (.inr m) = none then z₁.1 else h'))
    by_cases he : m = nO z₁.1
    · rw [← he, hm]
      simp
    · rw [drawCell_support_cells hz₁ _ (fun h => he (Sum.inr_injective h).symm)]
      simp [he]
  refine step1.trans ?_
  cases hst : st.2 (.inr m) with
  | some w =>
    rw [RelabelState.drawCell_run_of_cell_eq_some hst, pure_bind]
    simp only [hst, reduceCtorEq, ↓reduceIte]
    exact le_rfl
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none hst, bind_map_left]
    simp only [hst, ↓reduceIte]
    refine le_of_eq ?_
    calc _ = Pr{let y ← RY u C
                let a ← ($ᵗ St : ProbComp St)
                let g ← ($ᵗ St : ProbComp St)
                let h' ← ($ᵗ St : ProbComp St)}[Q y g a] := prEvent_bind_bind_swap _ _ _
      _ = Pr{let y ← RY u C
             let g ← ($ᵗ St : ProbComp St)
             let a ← ($ᵗ St : ProbComp St)
             let h' ← ($ᵗ St : ProbComp St)}[Q y g a] :=
          prEvent_bind_congr_of_support _ _ _ fun y _ => prEvent_bind_bind_swap _ _ _
      _ = Pr{let y ← RY u C
             let g ← ($ᵗ St : ProbComp St)
             let h' ← ($ᵗ St : ProbComp St)
             let a ← ($ᵗ St : ProbComp St)}[Q y g a] :=
          prEvent_bind_congr_of_support _ _ _ fun y _ => prEvent_bind_congr_of_support _ _ _
            fun g _ => prEvent_bind_map_swap _ _ _
      _ = _ := prEvent_bind_congr_of_support _ _ _ fun y _ => prEvent_bind_congr_of_support _ _ _
            fun g _ => OracleComp.prEvent_bind_const _ _

/-- The R-state map of an honest step. -/
def Φh (u : (hashSpec Cr).Domain) (T : Tc) (C : PubG.QueryCache) (G : GLT)
    (y : (hashSpec Cr).Range u) (g₁ g₂ : St) : Tc × GS :=
  (T, (cset u C y, gset (gset G (u, false) g₁) (u, true) g₂))

theorem romGE_hon_pr (u : (hashSpec Cr).Domain) (T : Tc) (C : PubG.QueryCache) (G : GLT)
    (Q : (hashSpec Cr).Range u × (Tc × GS) → Prop) :
    Pr{let z ← (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ gG.eagerImpl ((liftT (honG u)).run T)).run ((C, G) : GS)}[Q z] =
      Pr{let y ← RY u C
         let g₁ ← ($ᵗ St : ProbComp St)
         let g₂ ← ($ᵗ St : ProbComp St)}[Q (y, Φh u T C G y g₁ g₂)] := by
  rw [(romGE_hon_eqD u T C G).prEvent_eq]
  simp only [prEvent_norm, Φh]

theorem not_badJ_iff {s : σJ} (hs : ¬ badJ s) (l : List (QT Dsk).Domain) (b : Bool) (x : DS × (Tc × GS)) :
    ¬ badJ (x.1, x.2, (l, s.2.2.2 || b)) ↔ b = false := by
  simp only [badJ] at hs ⊢
  simp [Bool.eq_false_iff.2 hs]

open Classical in
/-- `updH` in terms of `cset`, `gset` and `flagH`. -/
theorem updH_eq (t : (hashSpec Cr).Domain) (L L' : LT) (r : Tc × GS) (h h' : St) :
    updH t L L' r h h' =
      ((r.1, (cset t r.2.1 (ansOf t (lab L' (finNd L' t))),
        gset (gset r.2.2 (t, false)
          (if (L (.inr (finNd L' t)) = none ∧ innNd t ≠ some (finNd L' t)) then
            splice t h (lab L' (finNd L' t)) else h)) (t, true)
          (if (match innNd t with | some m => L (.inr m) = none | none => False) then
            (match innNd t with | some m => lab L' m | none => 0) else h'))),
        decide (flagH r.2.1 t (L (.inr (finNd L' t)) = none ∧ innNd t ≠ some (finNd L' t))
          (lab L' (finNd L' t)))) := rfl

theorem pr_inner {X : Type} (A B : ProbComp St) (F : St → St → X) (E : X → Prop)
    (E2 : St → St → Prop) (h : ∀ a b, E (F a b) ↔ E2 a b) :
    prEvent ((fun z => E z) <$> (A >>= fun a => B >>= fun b => pure (F a b))) =
      prEvent (A >>= fun a => (fun b => E2 a b) <$> B) := by
  simp only [map_bind, map_pure]
  congr 1
  refine bind_congr fun a => ?_
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun b => ?_
  simp only [Function.comp, h a b]

/-- **Domination at an honest `Thash` query.** -/
theorem dom_thash (k : Bytes 16) (ps : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) (s : σJ)
    (hs : ¬ badJ s) (Q : (QT Dsk).Range (.inr (.inr (.inl (.thash ps a xs)))) × (Tc × GS) → Prop) :
    Pr{let z ← (J k (.inr (.inr (.inl (.thash ps a xs))))).run s}[Q (z.1, πR z.2) ∧ ¬ badJ z.2] ≤
      Pr{let z ← (romGE k (.inr (.inr (.inl (.thash ps a xs))))).run (πR s)}[Q z] := by
  obtain ⟨d, ⟨T, C, G⟩, l, fl⟩ := s
  have e : (romGE k (.inr (.inr (.inl (.thash ps a xs))))).run (πR (d, (T, C, G), l, fl)) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ gG.eagerImpl
        ((liftT (honG (.inl (.thash ps a xs)))).run T)).run ((C, G) : GS) := rfl
  rw [e]
  refine le_of_le_of_eq ?_ (romGE_hon_pr (.inl (.thash ps a xs)) T C G Q).symm
  rw [J_run, defH_thash, bind_map_left, map_bind]
  have hs' : fl = false := by simpa [badJ] using hs
  subst hs'
  refine le_of_eq_of_le ?_ (core1 (.inl (.thash ps a xs)) C
    (ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2)) d.1
    (d.1.2 (.inr (ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2))) = none) Iff.rfl
    (fun y g h' => Q (y, Φh (.inl (.thash ps a xs)) T C G y g h')))
  refine prEvent_bind_congr_of_support _ _ _ fun z' hz' => pr_inner _ _ _ _ _ fun h h' => ?_
  have hz := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz').2
  simp only [πR, badJ, upd, honT]
  rw [updH_eq]
  have e2 : lab z'.2.2 (finNd z'.2.2 (.inl (.thash ps a xs))) = z'.1 := by
    simp only [lab, finNd, hz, Option.getD_some]
  have hi : ¬ (match innNd (.inl (.thash ps a xs)) with
      | some m => d.1.2 (.inr m) = none | none => False) := by simp [innNd]
  rw [if_neg hi]
  by_cases hf : d.1.2 (.inr (ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2))) = none
  · have hf' : d.1.2 (.inr (finNd z'.2.2 (.inl (.thash ps a xs)))) = none ∧
        innNd (.inl (.thash ps a xs)) ≠ some (finNd z'.2.2 (.inl (.thash ps a xs))) :=
      ⟨hf, by simp [innNd]⟩
    rw [if_pos hf', if_pos hf, e2]
    have e1 : (d.1.2 (.inr (finNd z'.2.2 (.inl (.thash ps a xs)))) = none ∧
        innNd (.inl (.thash ps a xs)) ≠ some (finNd z'.2.2 (.inl (.thash ps a xs)))) =
        (d.1.2 (.inr (ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2))) = none) :=
      propext ⟨And.left, fun h => hf'⟩
    rw [e1]
    simp only [Bool.false_or, decide_eq_true_eq]
    exact Iff.rfl
  · have hf' : ¬ (d.1.2 (.inr (finNd z'.2.2 (.inl (.thash ps a xs)))) = none ∧
        innNd (.inl (.thash ps a xs)) ≠ some (finNd z'.2.2 (.inl (.thash ps a xs)))) :=
      fun h => hf h.1
    rw [if_neg hf', if_neg hf, e2]
    have e1 : (d.1.2 (.inr (finNd z'.2.2 (.inl (.thash ps a xs)))) = none ∧
        innNd (.inl (.thash ps a xs)) ≠ some (finNd z'.2.2 (.inl (.thash ps a xs)))) =
        (d.1.2 (.inr (ndOf (sb128 ps :: (tblocks a xs).1 :: (tblocks a xs).2))) = none) :=
      propext ⟨And.left, fun h => absurd h hf⟩
    rw [e1]
    simp only [Bool.false_or, decide_eq_true_eq]
    exact Iff.rfl

/-- **Domination at a PRF query.** -/
theorem dom_prf (k : Bytes 16) (dd : Dsk) (s : σJ)
    (hs : ¬ badJ s) (Q : (QT Dsk).Range (.inr (.inl (.inr dd))) × (Tc × GS) → Prop) :
    Pr{let z ← (J k (.inr (.inl (.inr dd)))).run s}[Q (z.1, πR z.2) ∧ ¬ badJ z.2] ≤
      Pr{let z ← (romGE k (.inr (.inl (.inr dd)))).run (πR s)}[Q z] := by
  obtain ⟨d, ⟨T, C, G⟩, l, fl⟩ := s
  have e : (romGE k (.inr (.inl (.inr dd)))).run (πR (d, (T, C, G), l, fl)) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ gG.eagerImpl
        ((liftT (honG (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))).run T)).run ((C, G) : GS) := rfl
  rw [e]
  refine le_of_le_of_eq ?_ (romGE_hon_pr (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) T C G Q).symm
  rw [J_run, defH_prf, bind_map_left, map_bind]
  have hs' : fl = false := by simpa [badJ] using hs
  subst hs'
  refine le_of_eq_of_le ?_ (core1 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) C
    (ndOf [sb128 dd.1, blk128 dd.2 k]) d.1
    (d.1.2 (.inr (ndOf [sb128 dd.1, blk128 dd.2 k])) = none) Iff.rfl
    (fun y g h' => Q (y, Φh (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) T C G y g h')))
  refine prEvent_bind_congr_of_support _ _ _ fun z' hz' => pr_inner _ _ _ _ _ fun h h' => ?_
  have hz := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz').2
  simp only [πR, badJ, upd, honT]
  rw [updH_eq]
  have hn : ∀ L, finNd L (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) =
      ndOf [sb128 dd.1, blk128 dd.2 k] := fun L => by
    exact congrArg ndOf (prf_walk dd k).symm
  have e2 : lab z'.2.2 (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k]))) = z'.1 := by
    rw [hn]; simp only [lab, hz, Option.getD_some]
  have hi : ¬ (match innNd (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) with
      | some m => d.1.2 (.inr m) = none | none => False) := by simp [innNd]
  rw [if_neg hi]
  by_cases hf : d.1.2 (.inr (ndOf [sb128 dd.1, blk128 dd.2 k])) = none
  · have hf' : d.1.2 (.inr (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) = none ∧
        innNd (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) ≠ some (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k]))) :=
      ⟨by rw [hn]; exact hf, by simp [innNd]⟩
    rw [if_pos hf', if_pos hf, e2]
    have e1 : (d.1.2 (.inr (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) = none ∧
        innNd (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) ≠ some (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) =
        (d.1.2 (.inr (ndOf [sb128 dd.1, blk128 dd.2 k])) = none) :=
      propext ⟨fun h => by rw [hn] at h; exact h.1, fun h => hf'⟩
    rw [e1]
    simp only [Bool.false_or, decide_eq_true_eq]
    exact Iff.rfl
  · have hf' : ¬ (d.1.2 (.inr (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) = none ∧
        innNd (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) ≠ some (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) :=
      fun h => hf (by rw [hn] at h; exact h.1)
    rw [if_neg hf', if_neg hf, e2]
    have e1 : (d.1.2 (.inr (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) = none ∧
        innNd (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])) ≠ some (finNd z'.2.2 (.inl (.thash dd.1 (Cr.adrsToKey dd.2.1) [k])))) =
        (d.1.2 (.inr (ndOf [sb128 dd.1, blk128 dd.2 k])) = none) :=
      propext ⟨fun h => by rw [hn] at h; exact h.1, fun h => absurd h hf⟩
    rw [e1]
    simp only [Bool.false_or, decide_eq_true_eq]
    exact Iff.rfl

/-- **Domination at an honest `H_msg` query.** -/
theorem dom_hmsg (k : Bytes 16) (R ps pr : Bytes 16) (M : List UInt8) (s : σJ)
    (hs : ¬ badJ s) (Q : (QT Dsk).Range (.inr (.inr (.inl (.hmsg R ps pr M)))) × (Tc × GS) → Prop) :
    Pr{let z ← (J k (.inr (.inr (.inl (.hmsg R ps pr M))))).run s}[Q (z.1, πR z.2) ∧ ¬ badJ z.2] ≤
      Pr{let z ← (romGE k (.inr (.inr (.inl (.hmsg R ps pr M))))).run (πR s)}[Q z] := by
  obtain ⟨d, ⟨T, C, G⟩, l, fl⟩ := s
  have e : (romGE k (.inr (.inr (.inl (.hmsg R ps pr M))))).run (πR (d, (T, C, G), l, fl)) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ gG.eagerImpl
        ((liftT (honG (.inl (.hmsg R ps pr M)))).run T)).run ((C, G) : GS) := rfl
  rw [e]
  refine le_of_le_of_eq ?_ (romGE_hon_pr (.inl (.hmsg R ps pr M)) T C G Q).symm
  have hs' : fl = false := by simpa [badJ] using hs
  subst hs'
  refine le_of_eq_of_le ?_ (core2 (.inl (.hmsg R ps pr M)) C (ndOf (iblocksH R ps pr M))
    (fun X => ndOf (oblocksH R ps X)) d.1
    (fun y g g' => Q (y, Φh (.inl (.hmsg R ps pr M)) T C G y g g')))
  rw [J_run, defH_hmsg, bind_assoc, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun z₁ hz₁ => ?_
  rw [bind_map_left, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun z₂ hz₂ => pr_inner _ _ _ _ _ fun h h' => ?_
  have h1 := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz₁).2
  have h2 := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz₂).2
  have eX : lab z₂.2.2 (ndOf (iblocksH R ps pr M)) = z₁.1 := by
    by_cases he : ndOf (iblocksH R ps pr M) = ndOf (oblocksH R ps z₁.1)
    · rw [RelabelState.drawCell_run_of_cell_eq_some (he ▸ h1), support_pure,
        Set.mem_singleton_iff] at hz₂
      rw [hz₂]; simp only [lab, h1, Option.getD_some]
    · rw [lab, drawCell_support_cells hz₂ _ (fun h => he (Sum.inr_injective h)), h1,
        Option.getD_some]
  have eN : finNd z₂.2.2 (.inl (.hmsg R ps pr M)) = ndOf (oblocksH R ps z₁.1) := by
    simp only [finNd, eX]
  have eV : lab z₂.2.2 (finNd z₂.2.2 (.inl (.hmsg R ps pr M))) = z₂.1 := by
    rw [eN]; simp only [lab, h2, Option.getD_some]
  simp only [πR, badJ, upd, honT]
  rw [updH_eq]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [eV]
  by_cases hA : d.1.2 (.inr (ndOf (oblocksH R ps z₁.1))) = none <;>
  by_cases hB : ndOf (iblocksH R ps pr M) = ndOf (oblocksH R ps z₁.1) <;>
  by_cases hX : d.1.2 (.inr (ndOf (iblocksH R ps pr M))) = none
  all_goals
    try have hB' : (ndOf (iblocksH R ps pr M) = ndOf (oblocksH R ps z₁.1)) = True := eq_true hB
    try have hB' : (ndOf (iblocksH R ps pr M) = ndOf (oblocksH R ps z₁.1)) = False := eq_false hB
    try have hA' : d.1.2 (.inr (finNd z₂.2.2 (.inl (.hmsg R ps pr M)))) = none := (by rw [eN]; exact hA)
    try have hA' : ¬ d.1.2 (.inr (finNd z₂.2.2 (.inl (.hmsg R ps pr M)))) = none := (by rw [eN]; exact hA)
    simp only [eN, hA, hA', hB', hX, innNd, eX, Option.some.injEq, ne_eq, not_true_eq_false,
      not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte, ansOf, Φh]

/-- **Domination at an honest `PRF_msg` query.** -/
theorem dom_prfmsg (k : Bytes 16) (k' o : Bytes 16) (M : List UInt8) (s : σJ)
    (hs : ¬ badJ s) (Q : (QT Dsk).Range (.inr (.inr (.inr (k', o, M)))) × (Tc × GS) → Prop) :
    Pr{let z ← (J k (.inr (.inr (.inr (k', o, M))))).run s}[Q (z.1, πR z.2) ∧ ¬ badJ z.2] ≤
      Pr{let z ← (romGE k (.inr (.inr (.inr (k', o, M))))).run (πR s)}[Q z] := by
  obtain ⟨d, ⟨T, C, G⟩, l, fl⟩ := s
  have e : (romGE k (.inr (.inr (.inr (k', o, M))))).run (πR (d, (T, C, G), l, fl)) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ gG.eagerImpl
        ((liftT (honG (.inr ⟨k', o, M⟩))).run T)).run ((C, G) : GS) := rfl
  rw [e]
  refine le_of_le_of_eq ?_ (romGE_hon_pr (.inr ⟨k', o, M⟩) T C G Q).symm
  have hs' : fl = false := by simpa [badJ] using hs
  subst hs'
  refine le_of_eq_of_le ?_ (core2 (.inr ⟨k', o, M⟩) C (ndOf (ikey k' :: iblocks o M))
    (fun X => ndOf [okey k', oblock X]) d.1
    (fun y g g' => Q (y, Φh (.inr ⟨k', o, M⟩) T C G y g g')))
  rw [J_run, defH_prfmsg, bind_assoc, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun z₁ hz₁ => ?_
  rw [bind_map_left, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun z₂ hz₂ => pr_inner _ _ _ _ _ fun h h' => ?_
  have h1 := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz₁).2
  have h2 := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz₂).2
  have eX : lab z₂.2.2 (ndOf (ikey k' :: iblocks o M)) = z₁.1 := by
    by_cases he : ndOf (ikey k' :: iblocks o M) = ndOf [okey k', oblock z₁.1]
    · rw [RelabelState.drawCell_run_of_cell_eq_some (he ▸ h1), support_pure,
        Set.mem_singleton_iff] at hz₂
      rw [hz₂]; simp only [lab, h1, Option.getD_some]
    · rw [lab, drawCell_support_cells hz₂ _ (fun h => he (Sum.inr_injective h)), h1,
        Option.getD_some]
  have eN : finNd z₂.2.2 (.inr ⟨k', o, M⟩) = ndOf [okey k', oblock z₁.1] := by
    simp only [finNd, eX]
  have eV : lab z₂.2.2 (finNd z₂.2.2 (.inr ⟨k', o, M⟩)) = z₂.1 := by
    rw [eN]; simp only [lab, h2, Option.getD_some]
  simp only [πR, badJ, upd, honT]
  rw [updH_eq]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [eV]
  by_cases hA : d.1.2 (.inr (ndOf [okey k', oblock z₁.1])) = none <;>
  by_cases hB : ndOf (ikey k' :: iblocks o M) = ndOf [okey k', oblock z₁.1] <;>
  by_cases hX : d.1.2 (.inr (ndOf (ikey k' :: iblocks o M))) = none
  all_goals
    try have hB' : (ndOf (ikey k' :: iblocks o M) = ndOf [okey k', oblock z₁.1]) = True := eq_true hB
    try have hB' : (ndOf (ikey k' :: iblocks o M) = ndOf [okey k', oblock z₁.1]) = False := eq_false hB
    try have hA' : d.1.2 (.inr (finNd z₂.2.2 (.inr ⟨k', o, M⟩))) = none := (by rw [eN]; exact hA)
    try have hA' : ¬ d.1.2 (.inr (finNd z₂.2.2 (.inr ⟨k', o, M⟩))) = none := (by rw [eN]; exact hA)
    simp only [eN, hA, hA', hB', hX, innNd, eX, Option.some.injEq, ne_eq, not_true_eq_false,
      not_false_eq_true, and_true, and_false, true_and, false_and, ↓reduceIte, ansOf, Φh]

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.dom_thash
#print axioms Ideal.Direct.Rom.dom_prf
#print axioms Ideal.Direct.Rom.dom_hmsg
#print axioms Ideal.Direct.Rom.dom_prfmsg
