import Ideal.Direct.CoupleDomH

/-!
# Domination of the joint handler at a forger cell and at a coin; `DomJ` (`status/DIRECT.md` §14)

* `relabel_ans`: the D answer at a forger cell is the merged value if present, else uniform;
* `romGE_port_*`: the R step at a cell (cached / relevant / inner / fresh), in distribution;
* `dom_port`, `dom_coin`, and **`domJ`**: every row of the table of §13.1 is dominated, so
  `DomJ` holds.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal SampleableType

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-- **The D answer at a forger cell**: the merged value if present, else uniform. -/
theorem relabel_ans (q : St × Blk) (st : MD.RS St Blk) :
    (fun z => z.1) <$> (Gs.relabelImpl (.inl (.inr q))).run st =ᵈ
      (match Gs.merge st q with
        | some w => (pure w : ProbComp St)
        | none => ($ᵗ St : ProbComp St)) := by
  rw [LGraph.relabelImpl_run_pub]
  by_cases h : ∃ k vs, Gs.childVals st k = some vs ∧ Gs.pt k vs = q
  · rw [dif_pos h]
    have hm : Gs.merge st q = (st.2 (.inr h.choose)).map
        (cast (Gs.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) := by
      rw [LGraph.merge, QueryCache.ofFn_apply, dif_pos h]
    rw [hm]
    cases hc : st.2 (.inr h.choose) with
    | some w =>
      rw [RelabelState.drawCell_run_of_cell_eq_some hc]
      simp only [map_pure, Prod.map, Option.map_some]
      exact EvalDistEq.refl _
    | none =>
      rw [RelabelState.drawCell_run_of_cell_eq_none hc]
      simp only [Functor.map_map, Prod.map, Option.map_none, cast_eq]
      exact EvalDistEq.of_forall_prEvent_eq fun p => by
        rw [prEvent_map]
  · rw [dif_neg h, LGraph.merge_apply_of_not_exists Gs h, Functor.map_map, randomOracle.run_eq]
    cases hc : st.1 q with
    | some w => simp only [map_pure]; exact EvalDistEq.refl _
    | none =>
      simp only [map_bind, map_pure]
      exact EvalDistEq.of_forall_prEvent_eq fun p => by
        rw [← bind_pure_comp]
        simp only [prEvent_norm]

/-- **A forger-cell step of `J`, read through the answer, the R state and the flag.** -/
theorem J_port_eqD (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (s : σJ) :
    (fun z => (z.1, πR z.2, z.2.2.2.2)) <$> (J k (.inr (.inl (.inl (pk, q))))).run s =ᵈ
      ((match Gs.merge s.1.1 q with
        | some w => (pure w : ProbComp St)
        | none => ($ᵗ St : ProbComp St)) >>= fun v => ($ᵗ St : ProbComp St) >>= fun h =>
          ($ᵗ St : ProbComp St) >>= fun h' =>
            pure (v, (updP pk q v (Gs.merge s.1.1 q = none) s.2.1 h).1,
              s.2.2.2 || (updP pk q v (Gs.merge s.1.1 q = none) s.2.1 h).2)) := by
  rw [J_run, defH_port]
  have e : ((fun z => (z.1, πR z.2, z.2.2.2.2)) <$>
      (((fun z => ((z.1 : (QT Dsk).Range (.inr (.inl (.inl (pk, q))))), (z.2, s.1.2))) <$>
        (Gs.relabelImpl (.inl (.inr q))).run s.1.1) >>= fun z =>
        ($ᵗ St : ProbComp St) >>= fun h => ($ᵗ St : ProbComp St) >>= fun h' =>
          pure (z.1, (z.2, (upd k (.inr (.inl (.inl (pk, q)))) s.1 z.1 z.2 s.2.1 h h').1,
            (s.2.2.1 ++ [.inr (.inl (.inl (pk, q)))],
              s.2.2.2 || (upd k (.inr (.inl (.inl (pk, q)))) s.1 z.1 z.2 s.2.1 h h').2))))) =
      ((fun z => z.1) <$> (Gs.relabelImpl (.inl (.inr q))).run s.1.1) >>= fun v =>
        ($ᵗ St : ProbComp St) >>= fun h => ($ᵗ St : ProbComp St) >>= fun h' =>
          pure (v, (updP pk q v (Gs.merge s.1.1 q = none) s.2.1 h).1,
            s.2.2.2 || (updP pk q v (Gs.merge s.1.1 q = none) s.2.1 h).2) := by
    simp only [map_bind, bind_map_left, map_pure]
    rfl
  rw [e]
  exact EvalDistEq.bind_left (relabel_ans q s.1.1) _

/-! ## The R side at a forger cell -/

theorem ge_port_some (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) {v : St} (hq : T q = some v)
    (G : GS) :
    (simulateQ gG.eagerImpl ((simStepG pk q).run T)).run G = pure ((v, T), G) := by
  show (simulateQ gG.eagerImpl (simStepG pk q T)).run G = _
  unfold simStepG
  simp only [hq, simulateQ_pure, StateT.run_pure]

theorem ge_port_rel (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (hq : T q = none)
    {t : (hashSpec Cr).Domain} (ht : relQ pk T q = some t) (C : PubG.QueryCache) (G : GLT) :
    (simulateQ gG.eagerImpl ((simStepG pk q).run T)).run ((C, G) : GS) =ᵈ
      (RY t C >>= fun y => ($ᵗ St : ProbComp St) >>= fun g₀ =>
        pure ((overlay t y ((G (.inr (t, false))).getD g₀),
          T.cacheQuery q (overlay t y ((G (.inr (t, false))).getD g₀))),
          ((cset t C y, gset G (t, false) g₀) : GS))) := by
  show (simulateQ gG.eagerImpl (simStepG pk q T)).run ((C, G) : GS) =ᵈ _
  unfold simStepG
  simp only [hq, ht, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, eG_o,
    bind_map_left, eG_r]
  refine (EvalDistEq.bind_left (ro_eqD t C) _).trans ?_
  rw [bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun y _ => ?_
  rw [pure_bind]
  refine (EvalDistEq.bind_left (drawCell_eqD (t, false) (cset t C y, G)) _).trans ?_
  rw [bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun g₀ _ => ?_
  rw [pure_bind]

theorem ge_port_inn (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (hq : T q = none)
    (ht : relQ pk T q = none) {t : (hashSpec Cr).Domain} (hi : innQ pk T q = some t)
    (C : PubG.QueryCache) (G : GLT) :
    (simulateQ gG.eagerImpl ((simStepG pk q).run T)).run ((C, G) : GS) =ᵈ
      (($ᵗ St : ProbComp St) >>= fun g₀ =>
        pure (((G (.inr (t, true))).getD g₀, T.cacheQuery q ((G (.inr (t, true))).getD g₀)),
          ((C, gset G (t, true) g₀) : GS))) := by
  show (simulateQ gG.eagerImpl (simStepG pk q T)).run ((C, G) : GS) =ᵈ _
  unfold simStepG
  simp only [hq, ht, hi, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, eG_r]
  refine (EvalDistEq.bind_left (drawCell_eqD (t, true) (C, G)) _).trans ?_
  rw [bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun g₀ _ => ?_
  rw [pure_bind]

theorem ge_port_fresh (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (hq : T q = none)
    (ht : relQ pk T q = none) (hi : innQ pk T q = none) (G : GS) :
    (simulateQ gG.eagerImpl ((simStepG pk q).run T)).run G =
      ($ᵗ St : ProbComp St) >>= fun u => pure ((u, T.cacheQuery q u), G) := by
  show (simulateQ gG.eagerImpl (simStepG pk q T)).run G = _
  unfold simStepG
  simp only [hq, ht, hi, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    eG_fresh, bind_map_left]

/-! ## Probability helpers -/

theorem pr_const_le {α β : Type} (W : ProbComp α) (z₀ : β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ w, P w → Q z₀) : Pr{let w ← W}[P w] ≤ Pr{let z ← (pure z₀ : ProbComp β)}[Q z] := by
  by_cases hq : Q z₀
  · calc _ ≤ 1 := prEvent_le_one _
      _ = _ := by simp [hq]
  · refine le_of_eq_of_le ((prEvent_eq_zero_iff _ _).2 fun w _ hw => hq (h w hw)) zero_le

theorem pr_drop2 {α : Type} (A : ProbComp α) (P : α → Prop) :
    Pr{let v ← A
       let h ← ($ᵗ St : ProbComp St)
       let h' ← ($ᵗ St : ProbComp St)}[P v] = Pr{let v ← A}[P v] := by
  rw [map_eq_bind_pure_comp]
  refine prEvent_bind_congr_of_support _ _ _ fun v _ => ?_
  rw [OracleComp.prEvent_bind_const, prEvent_def, prEvent_def, map_eq_bind_pure_comp]
  show 𝒟[($ᵗ St : ProbComp St) >>= fun _ => (pure (P v) : ProbComp Prop)] {True} =
    𝒟[(pure (P v) : ProbComp Prop)] {True}
  rw [OracleComp.evalDist_bind_const]

/-! ## The R update at a forger cell, case by case -/

/-- The ghost-tail flag of a relevant cell. -/
def flagR (G : GLT) (t : (hashSpec Cr).Domain) (fv : Prop) (v : St) : Prop :=
  match G (.inr (t, false)) with
  | none => ¬ fv
  | some g => overlay t (ansOf t v) g ≠ v

/-- The inner-ghost flag of an inner cell. -/
def flagI (G : GLT) (t : (hashSpec Cr).Domain) (fv : Prop) (v : St) : Prop :=
  match G (.inr (t, true)) with
  | none => ¬ fv
  | some g => g ≠ v

open Classical in
theorem updP_some (pk : PublicKeyCore Cr) (q : St × Blk) (v : St) (fv : Prop) (T : Tc)
    (C : PubG.QueryCache) (G : GLT) (h : St) {v' : St} (hq : T q = some v') :
    updP pk q v fv (T, (C, G)) h = ((T, (C, G)), decide (v' ≠ v)) := by
  simp only [updP, hq]

open Classical in
theorem updP_rel (pk : PublicKeyCore Cr) (q : St × Blk) (v : St) (fv : Prop) (T : Tc)
    (C : PubG.QueryCache) (G : GLT) (h : St) (hq : T q = none) {t : (hashSpec Cr).Domain}
    (ht : relQ pk T q = some t) :
    updP pk q v fv (T, (C, G)) h = ((T.cacheQuery q v, (cset t C (ansOf t v),
      gset G (t, false) (splice t h v))), decide (flagH C t fv v ∨ flagR G t fv v)) := by
  simp only [updP, hq, ht]
  rfl

open Classical in
theorem updP_inn (pk : PublicKeyCore Cr) (q : St × Blk) (v : St) (fv : Prop) (T : Tc)
    (C : PubG.QueryCache) (G : GLT) (h : St) (hq : T q = none) (ht : relQ pk T q = none)
    {t : (hashSpec Cr).Domain} (hi : innQ pk T q = some t) :
    updP pk q v fv (T, (C, G)) h = ((T.cacheQuery q v, (C, gset G (t, true) v)),
      decide (flagI G t fv v)) := by
  simp only [updP, hq, ht, hi]
  rfl

open Classical in
theorem updP_fresh (pk : PublicKeyCore Cr) (q : St × Blk) (v : St) (fv : Prop) (T : Tc)
    (C : PubG.QueryCache) (G : GLT) (h : St) (hq : T q = none) (ht : relQ pk T q = none)
    (hi : innQ pk T q = none) :
    updP pk q v fv (T, (C, G)) h = ((T.cacheQuery q v, (C, G)), decide (¬ fv)) := by
  simp only [updP, hq, ht, hi]

theorem pr_drop1 {α : Type} (A : ProbComp α) (P : α → Prop) :
    Pr{let a ← A
       let a₁ ← ($ᵗ St : ProbComp St)}[P a] = Pr{let a ← A}[P a] := by
  rw [map_eq_bind_pure_comp]
  refine prEvent_bind_congr_of_support _ _ _ fun a _ => ?_
  rw [prEvent_def, prEvent_def, map_eq_bind_pure_comp]
  show 𝒟[($ᵗ St : ProbComp St) >>= fun _ => (pure (P a) : ProbComp Prop)] {True} =
    𝒟[(pure (P a) : ProbComp Prop)] {True}
  rw [OracleComp.evalDist_bind_const]

theorem lhs_drop (DA : ProbComp St) (E : St → St → Prop) :
    prEvent (DA >>= fun a => ($ᵗ St : ProbComp St) >>= fun a₁ => ($ᵗ St : ProbComp St) >>=
      fun _ => (pure (E a a₁) : ProbComp Prop)) =
      Pr{let a ← DA
         let a₁ ← ($ᵗ St : ProbComp St)}[E a a₁] := by
  refine prEvent_bind_congr_of_support _ _ _ fun a _ => ?_
  rw [map_eq_bind_pure_comp]
  refine prEvent_bind_congr_of_support _ _ _ fun a₁ _ => ?_
  exact OracleComp.prEvent_bind_const _ _

/-! ## Domination at a forger cell -/

theorem romGE_port_run (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (G : GS) :
    (romGE k (.inr (.inl (.inl (pk, q))))).run (T, G) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ gG.eagerImpl ((simStepG pk q).run T)).run G :=
  rfl

theorem R_fresh (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (C : PubG.QueryCache)
    (G : GLT) (hq : T q = none) (ht : relQ pk T q = none) (hi : innQ pk T q = none)
    (Q : St × (Tc × GS) → Prop) :
    Pr{let z ← (romGE k (.inr (.inl (.inl (pk, q))))).run (T, ((C, G) : GS))}[Q z] =
      Pr{let u ← ($ᵗ St : ProbComp St)}[Q (u, (T.cacheQuery q u, ((C, G) : GS)))] := by
  rw [romGE_port_run, ge_port_fresh pk q T hq ht hi]
  simp only [prEvent_norm]

theorem R_inn (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (C : PubG.QueryCache)
    (G : GLT) (hq : T q = none) (ht : relQ pk T q = none) {t : (hashSpec Cr).Domain}
    (hi : innQ pk T q = some t) (Q : St × (Tc × GS) → Prop) :
    Pr{let z ← (romGE k (.inr (.inl (.inl (pk, q))))).run (T, ((C, G) : GS))}[Q z] =
      Pr{let g₀ ← ($ᵗ St : ProbComp St)}[Q ((G (.inr (t, true))).getD g₀,
        (T.cacheQuery q ((G (.inr (t, true))).getD g₀), ((C, gset G (t, true) g₀) : GS)))] := by
  rw [romGE_port_run, ((ge_port_inn pk q T hq ht hi C G).map _).prEvent_eq]
  simp only [prEvent_norm]

theorem R_rel (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc) (C : PubG.QueryCache)
    (G : GLT) (hq : T q = none) {t : (hashSpec Cr).Domain} (ht : relQ pk T q = some t)
    (Q : St × (Tc × GS) → Prop) :
    Pr{let z ← (romGE k (.inr (.inl (.inl (pk, q))))).run (T, ((C, G) : GS))}[Q z] =
      Pr{let y ← RY t C
         let g₀ ← ($ᵗ St : ProbComp St)}[Q (overlay t y ((G (.inr (t, false))).getD g₀),
        (T.cacheQuery q (overlay t y ((G (.inr (t, false))).getD g₀)),
          ((cset t C y, gset G (t, false) g₀) : GS)))] := by
  rw [romGE_port_run, ((ge_port_rel pk q T hq ht C G).map _).prEvent_eq]
  simp only [prEvent_norm]

theorem pr2_zero {α β : Type} (A : ProbComp α) (B : ProbComp β) (P : α → β → Prop)
    (h : ∀ a b, ¬ P a b) : Pr{let a ← A
                               let b ← B}[P a b] = 0 := by
  have := (prEvent_eq_zero_iff (A >>= fun a => (fun b => (a, b)) <$> B) (fun x => P x.1 x.2)).2
    (fun x _ => h x.1 x.2)
  simpa only [prEvent_norm] using this

/-! ### The four cell cases, with the D answer and the update abstracted -/

section Cases

variable (T : Tc) (C : PubG.QueryCache) (G : GLT) (q : St × Blk) (Q : St × (Tc × GS) → Prop)
  (DA : ProbComp St) (fv : Prop) (hDA : fv → DA = ($ᵗ St : ProbComp St))
  (hDA' : ¬ fv → ∃ w, DA = pure w) (U : St → St → (Tc × GS) × Bool)

include hDA hDA' in
theorem G_fresh (fl : St → Bool) (hfl : ∀ a, fl a = true ↔ ¬ fv)
    (hU : ∀ a a₁, U a a₁ = ((T.cacheQuery q a, ((C, G) : GS)), fl a)) :
    Pr{let a ← DA
       let a₁ ← ($ᵗ St : ProbComp St)}[Q (a, (U a a₁).1) ∧ ¬ (U a a₁).2 = true] ≤
      Pr{let u ← ($ᵗ St : ProbComp St)}[Q (u, (T.cacheQuery q u, ((C, G) : GS)))] := by
  simp only [hU, hfl, not_not]
  by_cases hf : fv
  · rw [hDA hf]
    simp only [hf, and_true]
    exact (pr_drop1 _ _).le
  · rw [pr2_zero _ _ _ fun a b h => hf h.2]
    exact zero_le

theorem pr2_le_of {α β γ : Type} (A : ProbComp α) (B : ProbComp β) (P : α → β → Prop)
    (X : ProbComp γ) (R : γ → Prop) (c : Prop) (hc : c → ∀ x ∈ support X, R x)
    (h : ∀ a b, P a b → c) :
    Pr{let a ← A
       let b ← B}[P a b] ≤ Pr{let x ← X}[R x] := by
  by_cases hc' : c
  · calc _ ≤ 1 := prEvent_le_one _
      _ = _ := ((prEvent_eq_one_iff _ _).2 (hc hc')).symm
  · rw [pr2_zero _ _ _ fun a b hp => hc' (h a b hp)]
    exact zero_le

include hDA hDA' in
theorem G_inn (t : (hashSpec Cr).Domain) (fl : St → Bool) (hfl : ∀ a, fl a = true ↔ flagI G t fv a)
    (hU : ∀ a a₁, U a a₁ = ((T.cacheQuery q a, ((C, gset G (t, true) a) : GS)), fl a)) :
    Pr{let a ← DA
       let a₁ ← ($ᵗ St : ProbComp St)}[Q (a, (U a a₁).1) ∧ ¬ (U a a₁).2 = true] ≤
      Pr{let g₀ ← ($ᵗ St : ProbComp St)}[Q ((G (.inr (t, true))).getD g₀,
        (T.cacheQuery q ((G (.inr (t, true))).getD g₀), ((C, gset G (t, true) g₀) : GS)))] := by
  simp only [hU, hfl]
  cases hg : G (.inr (t, true)) with
  | none =>
    simp only [flagI, hg, not_not, Option.getD_none]
    by_cases hf : fv
    · rw [hDA hf]
      simp only [hf, and_true]
      exact (pr_drop1 _ _).le
    · rw [pr2_zero _ _ _ fun a b h => hf h.2]
      exact zero_le
  | some g =>
    simp only [flagI, hg, ne_eq, not_not, Option.getD_some]
    refine pr2_le_of _ _ _ _ _ (Q (g, (T.cacheQuery q g, ((C, G) : GS)))) (fun hq x _ => ?_)
      (fun a b h => ?_)
    · simp only [gset, hg]; exact hq
    · obtain ⟨h1, rfl⟩ := h
      simpa only [gset, hg] using h1

include hDA hDA' in
theorem G_some {v' : St} (fl : St → Bool) (hfl : ∀ a, fl a = true ↔ v' ≠ a)
    (hU : ∀ a a₁, U a a₁ = ((T, ((C, G) : GS)), fl a)) :
    Pr{let a ← DA
       let a₁ ← ($ᵗ St : ProbComp St)}[Q (a, (U a a₁).1) ∧ ¬ (U a a₁).2 = true] ≤
      Pr{let z ← (pure (v', (T, ((C, G) : GS))) : ProbComp _)}[Q z] := by
  simp only [hU, hfl, ne_eq, not_not]
  refine pr2_le_of _ _ _ _ _ (Q (v', (T, ((C, G) : GS)))) (fun hq x hx => ?_) (fun a b h => ?_)
  · rw [support_pure, Set.mem_singleton_iff] at hx; rw [hx]; exact hq
  · obtain ⟨h1, rfl⟩ := h; exact h1

include hDA hDA' in
theorem G_rel (t : (hashSpec Cr).Domain) (fl : St → Bool)
    (hfl : ∀ a, fl a = true ↔ (flagH C t fv a ∨ flagR G t fv a))
    (hU : ∀ a a₁, U a a₁ = ((T.cacheQuery q a, ((cset t C (ansOf t a),
      gset G (t, false) (splice t a₁ a)) : GS)), fl a)) :
    Pr{let a ← DA
       let a₁ ← ($ᵗ St : ProbComp St)}[Q (a, (U a a₁).1) ∧ ¬ (U a a₁).2 = true] ≤
      Pr{let y ← RY t C
         let g₀ ← ($ᵗ St : ProbComp St)}[Q (overlay t y ((G (.inr (t, false))).getD g₀),
        (T.cacheQuery q (overlay t y ((G (.inr (t, false))).getD g₀)),
          ((cset t C y, gset G (t, false) g₀) : GS)))] := by
  simp only [hU, hfl, not_or]
  cases hC : C (.inl t) with
  | some y₀ =>
    simp only [RY, hC, pure_bind]
    cases hg : G (.inr (t, false)) with
    | some g₁ =>
      simp only [flagH, flagR, hC, hg, ne_eq, not_not, Option.getD_some]
      refine pr2_le_of _ _ _ _ _ (Q (overlay t y₀ g₁, (T.cacheQuery q (overlay t y₀ g₁),
        ((C, G) : GS)))) (fun hq x _ => ?_) (fun a b h => ?_)
      · simpa only [cset, gset, hC, hg] using hq
      · obtain ⟨h1, h2, h3⟩ := h
        rw [← h2] at h3
        subst h3
        simpa only [cset, gset, hC, hg] using h1
    | none =>
      simp only [flagH, flagR, hC, hg, ne_eq, not_not, Option.getD_none]
      by_cases hf : fv
      · rw [hDA hf]
        simp only [hf, and_true]
        have e : ∀ a a₁ : St, (Q (a, (T.cacheQuery q a, ((cset t C (ansOf t a),
            gset G (t, false) (splice t a₁ a)) : GS))) ∧ y₀ = ansOf t a) =
            ((fun y g => Q (overlay t y g, (T.cacheQuery q (overlay t y g),
              ((C, gset G (t, false) g) : GS))) ∧ y₀ = y) (ansOf t a) (splice t a₁ a)) := by
          intro a a₁
          simp only [overlay_splice, cset, hC]
        simp only [e]
        rw [splice_unif t (fun p => Q (overlay t p.1 p.2, (T.cacheQuery q (overlay t p.1 p.2),
          ((C, gset G (t, false) p.2) : GS))) ∧ y₀ = p.1)]
        refine (prEvent_eq_conj_le _ _ y₀ (fun y g => Q (overlay t y g,
          (T.cacheQuery q (overlay t y g), ((C, gset G (t, false) g) : GS))))).trans_eq ?_
        simp only [cset, hC]
      · rw [pr2_zero _ _ _ fun a b h => hf h.2.2]
        exact zero_le
  | none =>
    simp only [RY, hC]
    by_cases hf : fv
    · rw [hDA hf]
      cases hg : G (.inr (t, false)) with
      | none =>
        simp only [flagH, flagR, hC, hg, hf, not_true_eq_false, not_false_eq_true, and_true,
          Option.getD_none]
        have e : ∀ a a₁ : St, Q (a, (T.cacheQuery q a, ((cset t C (ansOf t a),
            gset G (t, false) (splice t a₁ a)) : GS))) =
            ((fun y g => Q (overlay t y g, (T.cacheQuery q (overlay t y g),
              ((cset t C y, gset G (t, false) g) : GS)))) (ansOf t a) (splice t a₁ a)) := by
          intro a a₁
          simp only [overlay_splice]
        simp only [e]
        exact (splice_unif t (fun p => Q (overlay t p.1 p.2, (T.cacheQuery q (overlay t p.1 p.2),
          ((cset t C p.1, gset G (t, false) p.2) : GS))))).le
      | some g₁ =>
        simp only [flagH, flagR, hC, hg, hf, not_true_eq_false, not_false_eq_true, true_and,
          ne_eq, not_not, Option.getD_some]
        calc _ ≤ Pr{let a ← ($ᵗ St : ProbComp St)
                    let a₁ ← ($ᵗ St : ProbComp St)}[Q (overlay t (ansOf t a) g₁,
                  (T.cacheQuery q (overlay t (ansOf t a) g₁),
                    ((cset t C (ansOf t a), G) : GS)))] :=
              prEvent_bind_mono_of_support _ _ _ fun a _ => prEvent_mono _ _ _ fun a₁ h => by
                obtain ⟨h1, h2⟩ := h
                rw [h2]
                simpa only [gset, hg] using h1
          _ = Pr{let a ← ($ᵗ St : ProbComp St)}[Q (overlay t (ansOf t a) g₁,
                  (T.cacheQuery q (overlay t (ansOf t a) g₁),
                    ((cset t C (ansOf t a), G) : GS)))] := pr_drop1 _ _
          _ = Pr{let y ← ($ᵗ ((hashSpec Cr).Range t) : ProbComp _)}[Q (overlay t y g₁,
                  (T.cacheQuery q (overlay t y g₁), ((cset t C y, G) : GS)))] :=
              ansOf_unif t (fun y => Q (overlay t y g₁, (T.cacheQuery q (overlay t y g₁),
                ((cset t C y, G) : GS))))
          _ = _ := by
              rw [← pr_drop1 ($ᵗ ((hashSpec Cr).Range t) : ProbComp _)]
              simp only [gset, hg]
    · rw [pr2_zero _ _ _ fun a b h => h.2.1 (by simp only [flagH, hC]; exact hf)]
      exact zero_le

end Cases

/-- **Domination at a forger cell.** -/
theorem dom_port (k : Bytes 16) (pk : PublicKeyCore Cr) (q : St × Blk) (s : σJ) (hs : ¬ badJ s)
    (Q : St × (Tc × GS) → Prop) :
    Pr{let z ← (J k (.inr (.inl (.inl (pk, q))))).run s}[Q (z.1, πR z.2) ∧ ¬ badJ z.2] ≤
      Pr{let z ← (romGE k (.inr (.inl (.inl (pk, q))))).run (πR s)}[Q z] := by
  obtain ⟨d, ⟨T, C, G⟩, l, fl⟩ := s
  have hs' : fl = false := by simpa [badJ] using hs
  subst hs'
  have hconv : Pr{let z ← (J k (.inr (.inl (.inl (pk, q))))).run (d, (T, C, G), l, false)}[
      Q (z.1, πR z.2) ∧ ¬ badJ z.2] =
      Pr{let w ← (fun z => (z.1, πR z.2, z.2.2.2.2)) <$>
        (J k (.inr (.inl (.inl (pk, q))))).run (d, (T, C, G), l, false)}[
          Q (w.1, w.2.1) ∧ ¬ w.2.2 = true] := by
    rw [prEvent_map]; rfl
  rw [hconv]
  refine ((J_port_eqD k pk q (d, (T, C, G), l, false)).prEvent_eq
    (fun w => Q (w.1, w.2.1) ∧ ¬ w.2.2 = true)).trans_le ?_
  simp only [map_bind, map_pure, Bool.false_or]
  refine le_of_eq_of_le (lhs_drop _ (fun a a₁ =>
    Q (a, (updP pk q a (Gs.merge d.1 q = none) (T, (C, G)) a₁).1) ∧
      ¬ (updP pk q a (Gs.merge d.1 q = none) (T, (C, G)) a₁).2 = true)) ?_
  have hDA : (Gs.merge d.1 q = none) → (match Gs.merge d.1 q with
      | some w => (pure w : ProbComp St) | none => ($ᵗ St : ProbComp St)) = $ᵗ St := by
    intro h; rw [h]
  have hDA' : ¬ (Gs.merge d.1 q = none) → ∃ w, (match Gs.merge d.1 q with
      | some w => (pure w : ProbComp St) | none => ($ᵗ St : ProbComp St)) = pure w := by
    intro h
    cases hm : Gs.merge d.1 q with
    | none => exact absurd hm h
    | some w => exact ⟨w, rfl⟩
  rw [show πR (d, (T, C, G), l, false) = (T, ((C, G) : GS)) from rfl]
  rcases hq : T q with _ | v'
  · rcases ht : relQ pk T q with _ | t
    · rcases hi : innQ pk T q with _ | t
      · rw [R_fresh k pk q T C G hq ht hi]
        refine G_fresh (T := T) (C := C) (G := G) (q := q) (Q := Q) (fv := Gs.merge d.1 q = none) (hDA := hDA) (hDA' := hDA')
          (hU := fun a a₁ => updP_fresh pk q a _ T C G a₁ hq ht hi) (hfl := ?_)
        exact fun a => by simp only [decide_eq_true_eq]
      · rw [R_inn k pk q T C G hq ht hi]
        refine G_inn (T := T) (C := C) (G := G) (q := q) (Q := Q) (fv := Gs.merge d.1 q = none) (hDA := hDA) (hDA' := hDA')
          (hU := fun a a₁ => updP_inn pk q a _ T C G a₁ hq ht hi) (t := t) (hfl := ?_)
        exact fun a => by simp only [decide_eq_true_eq]
    · rw [R_rel k pk q T C G hq ht]
      refine G_rel (T := T) (C := C) (G := G) (q := q) (Q := Q) (fv := Gs.merge d.1 q = none) (hDA := hDA) (hDA' := hDA')
        (hU := fun a a₁ => updP_rel pk q a _ T C G a₁ hq ht) (t := t) (hfl := ?_)
      exact fun a => by simp only [decide_eq_true_eq]
  · rw [romGE_port_run, ge_port_some pk q T hq, map_pure]
    refine G_some (T := T) (C := C) (G := G) (Q := Q) (fv := Gs.merge d.1 q = none) (hDA := hDA) (hDA' := hDA')
      (hU := fun a a₁ => updP_some pk q a _ T C G a₁ hq) (hfl := ?_)
    exact fun a => by simp only [decide_eq_true_eq]

/-! ## Coins and `DomJ` -/

theorem coin_eqD (k : Bytes 16) (n : ℕ) (s : σJ) :
    (fun z => (z.1, πR z.2)) <$> (J k (.inl n)).run s =ᵈ (romGE k (.inl n)).run (πR s) := by
  have hR : (romGE k (.inl n)).run (πR s) = (fun u => (u, πR s)) <$> (unifSpec.query n : ProbComp _) := by
    unfold romGE
    rw [fuseS_run]
    show (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ gG.eagerImpl ((liftT (coinG n)).run (πR s).1)).run (πR s).2 = _
    rw [liftT_run, simulateQ_map, StateT.run_map, eG_coin, Functor.map_map, Functor.map_map]
  rw [hR, J_run, defH_coin, bind_map_left]
  simp only [map_bind, map_pure, upd, πR]
  refine (EvalDistEq.bind_congr_of_support _ fun u _ =>
    (EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_const _ _)).trans ?_
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.refl _

theorem dom_coin (k : Bytes 16) (n : ℕ) (s : σJ) (Q : _ → Prop) :
    Pr{let z ← (J k (.inl n)).run s}[Q (z.1, πR z.2) ∧ ¬ badJ z.2] ≤
      Pr{let z ← (romGE k (.inl n)).run (πR s)}[Q z] := by
  calc _ ≤ Pr{let z ← (J k (.inl n)).run s}[Q (z.1, πR z.2)] := prEvent_mono _ _ _ fun z h => h.1
    _ = Pr{let w ← (fun z => (z.1, πR z.2)) <$> (J k (.inl n)).run s}[Q w] := by
        rw [prEvent_map]
    _ = _ := (coin_eqD k n s).prEvent_eq Q

/-- **Step 3 of §13.4: every row of the table is dominated.** -/
theorem domJ : DomJ := by
  intro k t s _ hs Q
  rcases t with n | (⟨pk, q⟩ | dd) | (q | tq)
  · exact dom_coin k n s Q
  · exact dom_port k pk q s hs Q
  · exact dom_prf k dd s hs Q
  · rcases q with ⟨ps, a, xs⟩ | ⟨R, ps, pr, M⟩
    · exact dom_thash k ps a xs s hs Q
    · exact dom_hmsg k R ps pr M s hs Q
  · obtain ⟨k', o, M⟩ := tq
    exact dom_prfmsg k k' o M s hs Q

/-- **`DeferCoreGhostSufH` from the bad bound alone.** -/
theorem deferCoreGhostSufH_of_bad (hb : BadJS) : DeferCoreGhostSufH :=
  deferCoreGhostSufH_of_parts domJ hb

/-- **`DeferCoreGhostEufH` from the bad bound alone.** -/
theorem deferCoreGhostEufH_of_bad (hb : BadJE) : DeferCoreGhostEufH :=
  deferCoreGhostEufH_of_parts domJ hb

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.dom_port
#print axioms Ideal.Direct.Rom.domJ
#print axioms Ideal.Direct.Rom.deferCoreGhostSufH_of_bad
#print axioms Ideal.Direct.Rom.deferCoreGhostEufH_of_bad
