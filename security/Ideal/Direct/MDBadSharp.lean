import Ideal.Direct.MDBad

/-!
# The sharp collision bound, and the hop under a `¬ Bad` form of the remaining statement
(`status/DIRECT.md` §12)

`Direct/MDBad.lean` charges every operation of the deferred game the worst case `Q/|St|`.  Here
each operation is charged the size of the bad set *at its time*: the `i`-th operation costs at most
`(i + 1)/|St|`, so with `n` operations `Pr[Bad] ≤ n(n+1)/2 · 2^-256` (`prBad_defRun_sharp`).  The
deferred touches carry the pending charge `Σ_{j < #pending} (nV + j + 1)/|St|`, which is exactly
what the end fill costs from the current state (`prEvent_endFill_bad_sharp`); a step that grows
`nV` raises it by `#pending/|St|`, which the step's own charge `(nV + #pending + 1)/|St|` covers.

Consequence: **`3 · Pr[Bad] ≤ epsHalf`** (`bad3Suf`, `bad3Euf`).  This pays for removing `Bad`
from the remaining statement: `DeferSimSufNB` (the deferred game wins **and `Bad` fails**) suffices
for `MDHopSuf` with the SAME `epsHop` (`mdHopSuf_of_nb`), and `DeferSimSuf → DeferSimSufNB`
(`deferSimSufNB_of`), so the remaining hypothesis is strictly weaker than §11's.
-/

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct

/-! ## The supermartingale with a size-dependent charge -/

section SizeEngine

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- **Pending-charge supermartingale, charge depending on the size.**  A charged step out of a
state of size `k` costs `ε k` (`ε` monotone); the size grows by at most one per charged step. -/
theorem ex_hz_le_of_step_size (so : QueryImpl spec (StateT σ ProbComp)) (I P : σ → Prop)
    (Ψ : σ → ℝ≥0∞) (p : ι → Prop) [DecidablePred p] (ε : ℕ → ℝ≥0∞) (hε : Monotone ε)
    (size : σ → ℕ)
    (hI : ∀ t s, I s → ∀ z ∈ support ((so t).run s), I z.2)
    (habs : ∀ t s, I s → P s → ∀ z ∈ support ((so t).run s), P z.2)
    (hsize : ∀ t s, I s → ∀ z ∈ support ((so t).run s),
      size z.2 ≤ size s + (if p t then 1 else 0))
    (hstep : ∀ t s, I s → ¬ P s →
      ex ((so t).run s) (fun z => hz P Ψ z.2) ≤ Ψ s + (if p t then ε (size s) else 0))
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) (hs : I s) :
    ex ((simulateQ so oa).run s) (fun z => hz P Ψ z.2) ≤
      hz P Ψ s + ∑ i ∈ Finset.range n, ε (size s + i) := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, ex_pure]
    exact le_self_add
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [run_simulateQ_query_bind, ex_bind]
    set n' := if p t then n - 1 else n with hn'
    set d := if p t then 1 else 0 with hd
    have hrest : ∀ z ∈ support ((so t).run s),
        ex ((simulateQ so (k z.1)).run z.2) (fun z => hz P Ψ z.2) ≤
          hz P Ψ z.2 + ∑ i ∈ Finset.range n', ε (size s + d + i) := by
      intro z hz'
      refine (ih z.1 n' (hn.2 z.1) z.2 (hI t s hs z hz')).trans (add_le_add le_rfl ?_)
      have h1 := hsize t s hs z hz'
      exact Finset.sum_le_sum fun i _ => hε (by omega)
    have hcount : (∑ i ∈ Finset.range n', ε (size s + d + i)) + (if p t then ε (size s) else 0) ≤
        ∑ i ∈ Finset.range n, ε (size s + i) := by
      by_cases hpt : p t
      · have hn0 : 0 < n := hn.1.resolve_left (not_not.2 hpt)
        obtain ⟨n'', rfl⟩ : ∃ n'', n = n'' + 1 := ⟨n - 1, by omega⟩
        simp only [hn', hd, hpt, ite_true, Nat.add_sub_cancel]
        rw [Finset.sum_range_succ', add_zero]
        refine le_of_eq (congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_))
        congr 1
        omega
      · simp only [hn', hd, hpt, ite_false, add_zero]
        exact le_rfl
    by_cases hPs : P s
    · refine (ex_mono_of_support _ (g := fun _ => 1 + ∑ i ∈ Finset.range n', ε (size s + d + i))
        fun z hz' => (hrest z hz').trans ?_).trans ?_
      · exact le_of_eq (congrArg (· + _) (hz_of_P (habs t s hs hPs z hz')))
      · rw [ex_const, hz_of_P hPs]
        exact add_le_add le_rfl (le_trans le_self_add hcount)
    · refine (ex_mono_of_support _ hrest).trans ?_
      rw [ex_add, ex_const]
      calc _ ≤ (Ψ s + (if p t then ε (size s) else 0)) +
            ∑ i ∈ Finset.range n', ε (size s + d + i) := by
            gcongr; exact hstep t s hs hPs
        _ ≤ hz P Ψ s + ∑ i ∈ Finset.range n, ε (size s + i) := by
          rw [hz_of_not_P hPs, add_assoc]; gcongr; rw [add_comm]; exact hcount

end SizeEngine

namespace MD

variable {St Blk : Type}

/-! ## Arithmetic of the pending charge -/

/-- `F a m = Σ_{j < m} (a + j + 1)`: the end-fill cost of `m` pending cells from `a`. -/
def F (a m : ℕ) : ℕ := ∑ j ∈ Finset.range m, (a + j + 1)

theorem F_succ (a m : ℕ) : F a (m + 1) = F a m + (a + m + 1) := Finset.sum_range_succ _ _

theorem F_le (a a' m : ℕ) (h : a' ≤ a + 1) : F a' m ≤ F a m + m := by
  unfold F
  calc ∑ j ∈ Finset.range m, (a' + j + 1) ≤ ∑ j ∈ Finset.range m, ((a + j + 1) + 1) :=
        Finset.sum_le_sum fun j _ => by omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem two_mul_sum_succ (n : ℕ) : 2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-! ## The end fill, sharp -/

section EndFill

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] [Nonempty Blk]
  (IV : St)

theorem endFill_cons (st : RS St Blk) (c : Empty ⊕ Nd Blk) (l : List (Empty ⊕ Nd Blk)) :
    RelabelState.endFill (st, c :: l) =
      (RelabelState.drawCell c).run st >>= fun z => RelabelState.endFill (z.2, l) := by
  rw [RelabelState.endFill_eq_simulateQ_cellImpl, OracleSpec.queryAll_cons]
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
    RelabelState.cellImpl_apply]
  refine bind_congr fun z => ?_
  rw [RelabelState.endFill_eq_simulateQ_cellImpl]

theorem prEvent_bind_eq_ex {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ) (E : γ → Prop) :
    Pr{let y ← mx >>= f}[E y] = ex mx fun x => Pr{let y ← f x}[E y] := by
  rw [prEvent_eq_ex, ex_bind]
  exact congrArg (ex mx) (funext fun x => (prEvent_eq_ex _ _).symm)

/-- **The end fill fires `Bad` with probability at most `Σ_{j < #pending} (nV + j + 1)/|St|`.** -/
theorem prEvent_endFill_bad_sharp : ∀ (l : List (Empty ⊕ Nd Blk)) (st : RS St Blk),
    ¬ (mdG (Blk := Blk) IV).Bad st →
    Pr{let st' ← RelabelState.endFill (st, l)}[(mdG (Blk := Blk) IV).Bad st'] ≤
      (F (nV st) l.length : ℝ≥0∞) / Fintype.card St
  | [], st, hb => by
    classical
    rw [RelabelState.endFill_nil, prEvent_pure]
    simp [hb]
  | c :: l, st, hb => by
    rw [endFill_cons, prEvent_bind_eq_ex]
    have hpt : ∀ z ∈ support ((RelabelState.drawCell c).run st),
        Pr{let st' ← RelabelState.endFill (z.2, l)}[(mdG (Blk := Blk) IV).Bad st'] ≤
          propInd ((mdG (Blk := Blk) IV).Bad z.2) +
            ((F (nV st) l.length + l.length : ℕ) : ℝ≥0∞) / Fintype.card St := by
      intro z hz
      by_cases hbz : (mdG (Blk := Blk) IV).Bad z.2
      · rw [propInd_eq_one_iff.2 hbz]
        exact (prEvent_le_one _).trans le_self_add
      · rw [propInd_eq_zero_iff.2 hbz, zero_add]
        refine (prEvent_endFill_bad_sharp l z.2 hbz).trans (ENNReal.div_le_div_right ?_ _)
        exact_mod_cast F_le _ _ _ (nV_le_of_mem_support_drawCell hz)
    refine (ex_mono_of_support _ hpt).trans ?_
    rw [ex_add, ex_const, ← prEvent_eq_ex]
    refine (add_le_add (prEvent_draw_bad IV hb c) le_rfl).trans (le_of_eq ?_)
    rw [ENNReal.div_add_div_same, List.length_cons, F_succ]
    congr 1
    push_cast
    ring

end EndFill

/-! ## The deferred game, sharp -/

section Deferred

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] [Nonempty Blk]
  (IV : St)

/-- The pending charge: what the end fill of the pending touches costs from the current state. -/
noncomputable def pendF (s : RS St Blk × List (Empty ⊕ Nd Blk)) : ℝ≥0∞ :=
  (F (nV s.1) s.2.length : ℝ≥0∞) / Fintype.card St

/-- The charge of one operation at size `k`. -/
noncomputable def epsS (St : Type) [Fintype St] (k : ℕ) : ℝ≥0∞ :=
  ((k + 1 : ℕ) : ℝ≥0∞) / Fintype.card St

theorem epsS_mono : Monotone (epsS St) := fun a b h =>
  ENNReal.div_le_div_right (by exact_mod_cast Nat.succ_le_succ h) _

theorem pendF_le (st st' : RS St Blk) (l : List (Empty ⊕ Nd Blk)) (h : nV st' ≤ nV st + 1) :
    pendF (st', l) ≤ ((F (nV st) l.length + l.length : ℕ) : ℝ≥0∞) / Fintype.card St :=
  ENNReal.div_le_div_right (by exact_mod_cast F_le _ _ _ h) _

theorem pendF_add_eq (st : RS St Blk) (l : List (Empty ⊕ Nd Blk)) :
    pendF (st, l) + epsS St (dSize (st, l)) =
      ((F (nV st) l.length + l.length : ℕ) : ℝ≥0∞) / Fintype.card St +
        ((nV st + 1 : ℕ) : ℝ≥0∞) / Fintype.card St := by
  unfold pendF epsS dSize
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  congr 1
  push_cast
  ring

theorem dStep_sharp (t : (WL St Blk).Domain) (s : RS St Blk × List (Empty ⊕ Nd Blk))
    (hb : ¬ (mdG (Blk := Blk) IV).Bad s.1) :
    ex (((mdG (Blk := Blk) IV).deferredImpl t).run s)
        (fun z ↦ hz (fun s : RS St Blk × List (Empty ⊕ Nd Blk) ↦ (mdG (Blk := Blk) IV).Bad s.1)
          pendF z.2) ≤
      pendF s + (if isNU t = true then epsS St (dSize s) else 0) := by
  classical
  set P := fun s : RS St Blk × List (Empty ⊕ Nd Blk) ↦ (mdG (Blk := Blk) IV).Bad s.1
  obtain ⟨st, l⟩ := s
  have hdraw : ∀ c, ex ((fun z ↦ (z.1, (z.2, l))) <$> (RelabelState.drawCell c).run st)
      (fun z ↦ hz P pendF z.2) ≤ pendF (st, l) + epsS St (dSize (st, l)) := by
    intro c
    rw [ex_map]
    have hpt : ∀ w ∈ support ((RelabelState.drawCell c).run st),
        hz P pendF (w.2, l) ≤ propInd ((mdG (Blk := Blk) IV).Bad w.2) +
          ((F (nV st) l.length + l.length : ℕ) : ℝ≥0∞) / Fintype.card St := fun w hw =>
      (hz_le_propInd_add P pendF (w.2, l)).trans
        (add_le_add le_rfl (pendF_le st w.2 l (nV_le_of_mem_support_drawCell hw)))
    refine (ex_mono_of_support _ hpt).trans ?_
    rw [ex_add, ex_const, ← prEvent_eq_ex, pendF_add_eq, add_comm]
    exact add_le_add le_rfl (prEvent_draw_bad IV hb c)
  rcases t with ((n | t) | x) | (c | k)
  · rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_unif, Functor.map_map, ex_map]
    simp only [Function.comp_def, isNU, Bool.false_eq_true, ite_false, add_zero]
    rw [ex_const]
    exact (hz_le_propInd_add P pendF _).trans (by rw [propInd_eq_zero_iff.2 hb, zero_add])
  · rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_pub]
    simp only [isNU, ite_true]
    split_ifs with h
    · rw [Functor.map_map, ex_map]
      have := hdraw (.inr h.choose)
      rw [ex_map] at this
      exact this
    · rw [Functor.map_map, ex_map]
      refine le_trans (ex_mono_of_support _
        (g := fun _ ↦ ((F (nV st) l.length + l.length : ℕ) : ℝ≥0∞) / Fintype.card St)
        fun y hy ↦ ?_) ?_
      · simp only [Function.comp_apply]
        have hnb : ¬ P ((y.2, st.2), l) := by
          show ¬ (mdG (Blk := Blk) IV).Bad (y.2, st.2)
          rw [QueryImpl.withCaching_run_eq_cacheQuery _ hy]
          exact not_bad_ro IV hb h y.1
        rw [hz_of_not_P hnb]
        refine pendF_le st _ l ?_
        show nV (y.2, st.2) ≤ _
        rw [QueryImpl.withCaching_run_eq_cacheQuery _ hy]
        exact nV_ro_le st t y.1
      · rw [ex_const, pendF_add_eq]
        exact le_self_add
  · exact x.elim
  · rw [LGraph.deferredImpl_run_touch, ex_pure]
    show hz P pendF (st, l ++ [c]) ≤ _
    rw [hz_of_not_P (P := P) (s := (st, l ++ [c])) hb]
    simp only [isNU, ite_true]
    unfold pendF epsS dSize
    rw [ENNReal.div_add_div_same, List.length_append, List.length_singleton, F_succ]
    push_cast
    exact le_rfl
  · rw [LGraph.deferredImpl_run_read]
    simp only [isNU, ite_true]
    exact hdraw _

/-- **The bad event of the deferred game with its end fill, sharp**: with `n` non-coin
label-program queries, `Pr[Bad] ≤ Σ_{i < n} (i + 1)/|St|`. -/
theorem prBad_defRun_sharp {α : Type} (X : OracleComp (OSp St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP (simulateQ (labI IV) X) (fun i ↦ isNU i = true) n) :
    Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).deferredImpl (simulateQ (labI IV) X)).run
        ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[(mdG (Blk := Blk) IV).Bad st] ≤
      ((∑ i ∈ Finset.range n, (i + 1) : ℕ) : ℝ≥0∞) / Fintype.card St := by
  set G := mdG (Blk := Blk) IV
  set P := fun s : RS St Blk × List (Empty ⊕ Nd Blk) ↦ G.Bad s.1
  set A := (simulateQ G.deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
  have e0 : dSize (((∅, ∅), []) : RS St Blk × List (Empty ⊕ Nd Blk)) = 0 := by
    simp [dSize, nV_empty]
  have h1 : Pr{let z ← A; let st ← RelabelState.endFill z.2}[G.Bad st] =
      ex A fun z ↦ Pr{let st ← RelabelState.endFill z.2}[G.Bad st] := by
    have h0 : Pr{let z ← A; let st ← RelabelState.endFill z.2}[G.Bad st] =
        Pr{let st ← A >>= fun z ↦ RelabelState.endFill z.2}[G.Bad st] := by
      simp only [prEvent_norm]
    rw [h0, prEvent_bind_eq_ex]
  rw [h1]
  refine (ex_mono _ (g := fun z ↦ hz P pendF z.2) fun z ↦ ?_).trans ?_
  · by_cases hb : G.Bad z.2.1
    · rw [hz_of_P (P := P) hb]; exact prEvent_le_one _
    · rw [hz_of_not_P (P := P) hb]
      exact prEvent_endFill_bad_sharp IV z.2.2 z.2.1 hb
  · have h := ex_hz_le_of_step_size G.deferredImpl (fun _ ↦ True) P pendF
      (fun i ↦ isNU i = true) (epsS St) epsS_mono dSize (fun _ _ _ _ _ ↦ trivial)
      (fun t s _ hs z hz ↦ hs.mono _ (G.le_of_mem_support_deferredImpl hz))
      (fun t s _ z hz ↦ dSize_step IV t s z hz)
      (fun t s _ hs ↦ dStep_sharp IV t s hs)
      _ n hn ((∅, ∅), []) trivial
    refine h.trans (le_of_eq ?_)
    rw [hz_of_not_P (P := P) G.not_bad_empty, e0]
    simp only [pendF, nV_empty, List.length_nil, F, Finset.range_zero, Finset.sum_empty,
      Nat.cast_zero, ENNReal.zero_div, zero_add, epsS]
    rw [Nat.cast_sum]
    simp only [div_eq_mul_inv, Finset.sum_mul]

end Deferred

end MD

/-! ## `3 · Pr[Bad] ≤ epsHalf`, and the hop under `DeferSimSufNB` -/

namespace Rom

open SLHDSA SLHDSA.Security SignatureAlg Ideal.Realize Ideal.Realize.Prf

theorem three_bound (n Q : ℕ) (h : n ≤ Q) :
    3 * (((∑ i ∈ Finset.range n, (i + 1) : ℕ) : ℝ≥0∞) / Fintype.card St) ≤
      (((Q + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 255 := by
  rw [card_St, ← mul_div_assoc]
  have h2 : (2 : ℝ≥0∞) ^ 256 = 2 * 2 ^ 255 := by rw [← pow_succ']
  rw [h2]
  have e : ((Q + 1) ^ 2 : ℕ) = (2 * (Q + 1) ^ 2) / 2 := by omega
  rw [show ((((Q + 1) ^ 2 : ℕ)) : ℝ≥0∞) / 2 ^ 255 =
      (((2 * (Q + 1) ^ 2 : ℕ)) : ℝ≥0∞) / (2 * 2 ^ 255) by
    push_cast
    rw [ENNReal.mul_div_mul_left _ _ two_ne_zero ofNat_ne_top]]
  refine ENNReal.div_le_div_right ?_ _
  have hS := MD.two_mul_sum_succ n
  have : 3 * ∑ i ∈ Finset.range n, (i + 1) ≤ 2 * (Q + 1) ^ 2 := by nlinarith
  exact_mod_cast this

theorem bad3Run (X : OracleComp OS Bool) (Q : ℕ)
    (hX : IsQueryBoundP (simulateQ (MD.cellsR IV128) X) (fun i ↦ i.isRight = true) Q) :
    3 * Pr{let w ← defRun X}[Gs.Bad w.2] ≤ (((Q + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 255 := by
  rw [← defRun_prEvent X (fun _ st ↦ Gs.Bad st)]
  refine le_trans ?_ (three_bound Q Q le_rfl)
  gcongr
  exact MD.prBad_defRun_sharp IV128 X Q (MD.qb_labI IV128 X Q hX)

/-- **`3 · Pr[Bad] ≤ epsHalf` (SUF).** -/
theorem bad3Suf (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    3 * Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2] ≤ epsHalf qf qs ℓ := by
  have h := progS_comp S oR ($ᵗ (Bytes 16)) hqf hqs hlong hout
  rw [h1_suf] at h
  exact bad3Run _ (QAll qf qs ℓ) (h.mono (Nat.add_le_add_right (qPrf_le_QcAll qf qs ℓ) _))

/-- **`3 · Pr[Bad] ≤ epsHalf` (EUF).** -/
theorem bad3Euf (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    3 * Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2] ≤ epsHalf qf qs ℓ := by
  have h := progE_comp S oR ($ᵗ (Bytes 16)) hqf hqs hlong hout
  rw [h1_euf] at h
  exact bad3Run _ (QAll qf qs ℓ) (h.mono (Nat.add_le_add_right (qPrf_le_QcAll qf qs ℓ) _))

/-- **The remaining statement (SUF), `¬ Bad` form, not proved**: the deferred game of `XS` wins
with `Bad` failing at its filled final state with probability at most VCVio's SUF advantage of the
simulator plus `epsHalf + qs/2^128`.  Weaker than `DeferSimSuf` (`deferSimSufNB_of`). -/
def DeferSimSufNB : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[w.1 = true ∧ ¬ Gs.Bad w.2] ≤
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdv S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **The remaining statement (EUF), `¬ Bad` form, not proved.** -/
def DeferSimEufNB : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[w.1 = true ∧ ¬ Gs.Bad w.2] ≤
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdvE S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

theorem deferSimSufNB_of (h : DeferSimSuf) : DeferSimSufNB := fun S oR qf qs ℓ hqf hqs hlong hout =>
  (prEvent_mono _ _ _ fun _ hw => hw.1).trans (h S oR qf qs ℓ hqf hqs hlong hout)

theorem deferSimEufNB_of (h : DeferSimEuf) : DeferSimEufNB := fun S oR qf qs ℓ hqf hqs hlong hout =>
  (prEvent_mono _ _ _ fun _ hw => hw.1).trans (h S oR qf qs ℓ hqf hqs hlong hout)

theorem prEvent_split {β : Type} (mx : ProbComp β) (A B : β → Prop) :
    Pr{let w ← mx}[A w] ≤ Pr{let w ← mx}[A w ∧ ¬ B w] + Pr{let w ← mx}[B w] :=
  (prEvent_mono _ _ (fun w => (A w ∧ ¬ B w) ∨ B w) fun w hw => by tauto).trans
    (prEvent_or_le _ _ _)

/-- **The hop from `DeferSimSufNB`** (with `BadSuf` proved, sharp form): the same `epsHop`. -/
theorem mdHopSuf_of_nb (hD : DeferSimSufNB) : MDHopSuf := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (suf_le_deferred S oR _).trans ?_
  rw [← epsHalf_add]
  set p := Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2]
  have h1 := prEvent_split (defRun (XS S oR ($ᵗ (Bytes 16)))) (fun w => w.1 = true)
    (fun w => Gs.Bad w.2)
  have h2 := hD S oR qf qs ℓ hqf hqs hlong hout
  have h3 := bad3Suf S oR hqf hqs hlong hout
  calc _ ≤ (Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[w.1 = true ∧ ¬ Gs.Bad w.2] + p) +
        2 * p := add_le_add h1 le_rfl
    _ = Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[w.1 = true ∧ ¬ Gs.Bad w.2] + 3 * p := by
        ring
    _ ≤ (strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdv S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128) +
          epsHalf qf qs ℓ := add_le_add h2 h3
    _ = _ := by ring

/-- **The EUF hop from `DeferSimEufNB`.** -/
theorem mdHopEuf_of_nb (hD : DeferSimEufNB) : MDHopEuf := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (euf_le_deferred S oR _).trans ?_
  rw [← epsHalf_add]
  set p := Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2]
  have h1 := prEvent_split (defRun (XE S oR ($ᵗ (Bytes 16)))) (fun w => w.1 = true)
    (fun w => Gs.Bad w.2)
  have h2 := hD S oR qf qs ℓ hqf hqs hlong hout
  have h3 := bad3Euf S oR hqf hqs hlong hout
  calc _ ≤ (Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[w.1 = true ∧ ¬ Gs.Bad w.2] + p) +
        2 * p := add_le_add h1 le_rfl
    _ = Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[w.1 = true ∧ ¬ Gs.Bad w.2] + 3 * p := by
        ring
    _ ≤ (unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdvE S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128) +
          epsHalf qf qs ℓ := add_le_add h2 h3
    _ = _ := by ring

/-! ## The composed bounds under the remaining statement -/

section Composed

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
include hqf hqs hlong hout

theorem suf_rom_nb (hD : DeferSimSufNB) : sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  suf_rom_of_hop (mdHopSuf_of_nb hD) S oR hqf hqs hlong hout

theorem euf_rom_nb (hD : DeferSimEufNB) : eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  euf_rom_of_hop (mdHopEuf_of_nb hD) S oR hqf hqs hlong hout

theorem suf_rom_2_20_nb (hD : DeferSimSufNB) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  suf_rom_2_20 S oR hqf hqs hlong hout (mdHopSuf_of_nb hD) hf hs hℓ

theorem suf_rom_2_40_nb (hD : DeferSimSufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  suf_rom_2_40 S oR hqf hqs hlong hout (mdHopSuf_of_nb hD) hf hs hℓ

theorem suf_rom_2_64_nb (hD : DeferSimSufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  suf_rom_2_64 S oR hqf hqs hlong hout (mdHopSuf_of_nb hD) hf hs hℓ

theorem euf_rom_2_20_nb (hD : DeferSimEufNB) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  euf_rom_2_20 S oR hqf hqs hlong hout (mdHopEuf_of_nb hD) hf hs hℓ

theorem euf_rom_2_40_nb (hD : DeferSimEufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  euf_rom_2_40 S oR hqf hqs hlong hout (mdHopEuf_of_nb hD) hf hs hℓ

theorem euf_rom_2_64_nb (hD : DeferSimEufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  euf_rom_2_64 S oR hqf hqs hlong hout (mdHopEuf_of_nb hD) hf hs hℓ

end Composed

section ComposedPure

variable (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
include hqf hqs hlong hout

theorem sufP_rom_nb (hD : DeferSimSufNB) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  sufP_rom_of_hop (mdHopSuf_of_nb hD) S oR hqf hqs hlong hout

theorem eufP_rom_nb (hD : DeferSimEufNB) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  eufP_rom_of_hop (mdHopEuf_of_nb hD) S oR hqf hqs hlong hout

theorem sufP_rom_2_20_nb (hD : DeferSimSufNB) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  sufP_rom_2_20 S oR hqf hqs hlong hout (mdHopSuf_of_nb hD) hf hs hℓ

theorem sufP_rom_2_40_nb (hD : DeferSimSufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  sufP_rom_2_40 S oR hqf hqs hlong hout (mdHopSuf_of_nb hD) hf hs hℓ

theorem sufP_rom_2_64_nb (hD : DeferSimSufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  sufP_rom_2_64 S oR hqf hqs hlong hout (mdHopSuf_of_nb hD) hf hs hℓ

theorem eufP_rom_2_20_nb (hD : DeferSimEufNB) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  eufP_rom_2_20 S oR hqf hqs hlong hout (mdHopEuf_of_nb hD) hf hs hℓ

theorem eufP_rom_2_40_nb (hD : DeferSimEufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  eufP_rom_2_40 S oR hqf hqs hlong hout (mdHopEuf_of_nb hD) hf hs hℓ

theorem eufP_rom_2_64_nb (hD : DeferSimEufNB) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  eufP_rom_2_64 S oR hqf hqs hlong hout (mdHopEuf_of_nb hD) hf hs hℓ

end ComposedPure

end Rom

end Ideal.Direct

#print axioms Ideal.Direct.ex_hz_le_of_step_size
#print axioms Ideal.Direct.MD.prEvent_endFill_bad_sharp
#print axioms Ideal.Direct.MD.prBad_defRun_sharp
#print axioms Ideal.Direct.Rom.bad3Suf
#print axioms Ideal.Direct.Rom.bad3Euf
#print axioms Ideal.Direct.Rom.deferSimSufNB_of
#print axioms Ideal.Direct.Rom.mdHopSuf_of_nb
#print axioms Ideal.Direct.Rom.mdHopEuf_of_nb
#print axioms Ideal.Direct.Rom.sufP_rom_2_64_nb
#print axioms Ideal.Direct.Rom.eufP_rom_2_64_nb
