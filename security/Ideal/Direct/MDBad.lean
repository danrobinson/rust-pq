import Ideal.Direct.MDHop
import Ideal.Direct.CollBudget
import Ideal.Direct.Counts

/-!
# H4, collision part: the bad event of the Merkle–Damgård relabelling (`status/DIRECT.md` §12)

Proved here (unconditional): **`BadSuf`** and **`BadEuf`** of `Direct/MDHop.lean`.

* `bad_iff`-style facts: in the Merkle–Damgård graph, `Bad` of a relabelled state is a label
  collision, a label equal to `IV`, a label equal to the chaining input of a cached public cell,
  or a cached public cell at `IV` (`ptColl_imp`, `conflict_imp` of `MDCore` and their converses
  `ptColl_of_eq`, `ptColl_of_IV`, `conflict_of_lab`, `conflict_of_IV`).
* `not_bad_draw`: a fresh label `u` creates `Bad` only if `u` is a drawn label value, `IV`, or the
  chaining input of a cached public cell; `not_bad_ro`: a public cell cached off the node points
  creates no `Bad`.  Hence one draw fires `Bad` with probability at most `(nV + 1)/|St|`
  (`prEvent_draw_bad`), `nV` = number of drawn label values + number of chaining inputs of cached
  public cells.
* The end fill (`prEvent_endFill_bad`) and the deferred game (`prBad_defRun_le`), by the capped
  pending-charge supermartingale `ex_hz_le_of_step_cap`: the deferred touches are a pending
  charge `ε · #pending`, discharged by the end fill.  With `n` label/compression operations and the
  cap `Q ≥ n`: `Pr[Bad] ≤ n · Q / |St|`.
* The count: the label program `simulateQ labI X` makes at most as many non-coin queries as the
  real program `simulateQ cellsR X` makes compression queries (`qb_labI`); for `XS`/`XE` that is
  `≤ QAll` (`Counts.progS_comp`, `h1_suf`).
-/

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct

/-! ## Support size along a simulation -/

section SizeSupport

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- A size growing by at most one per charged query grows by at most the query bound. -/
theorem size_le_of_mem_support_run (so : QueryImpl spec (StateT σ ProbComp)) (p : ι → Prop)
    [DecidablePred p] (size : σ → ℕ)
    (hsize : ∀ t s, ∀ z ∈ support ((so t).run s), size z.2 ≤ size s + (if p t then 1 else 0))
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) :
    ∀ z ∈ support ((simulateQ so oa).run s), size z.2 ≤ size s + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    intro z hz
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have h1 := hsize t s y hy
    have h2 := ih y.1 _ (hn.2 y.1) y.2 z hz
    by_cases hpt : p t
    · have := hn.1.resolve_left (not_not.2 hpt)
      simp only [hpt, ite_true] at h1 h2
      omega
    · simp only [hpt, ite_false] at h1 h2
      omega

end SizeSupport

namespace MD

variable {St Blk : Type}

/-! ## The bad sets -/

section BadSets

/-- The drawn label values. -/
def labV (st : RS St Blk) : Set St := {v | ∃ c, st.2 c = some v}

/-- The chaining inputs of the cached public cells. -/
def cfV (st : RS St Blk) : Set St := {v | ∃ b, (st.1 (v, b)).isSome}

/-- The size of the bad set of one draw (without `IV`). -/
noncomputable def nV (st : RS St Blk) : ℕ := (labV st).ncard + (cfV st).ncard

theorem labV_empty : labV ((∅, ∅) : RS St Blk) = ∅ := by
  ext v; simp [labV]

theorem cfV_empty : cfV ((∅, ∅) : RS St Blk) = ∅ := by
  ext v; simp [cfV]

theorem nV_empty : nV ((∅, ∅) : RS St Blk) = 0 := by
  simp [nV, labV_empty, cfV_empty]

variable [DecidableEq St] [DecidableEq Blk] [Finite St]

theorem labV_cacheQuery_subset (st : RS St Blk) (c : Empty ⊕ Nd Blk) (u : St) :
    labV (st.1, st.2.cacheQuery c u) ⊆ insert u (labV st) := by
  rintro v ⟨c', hc'⟩
  by_cases h : c' = c
  · subst h
    rw [QueryCache.cacheQuery_self, Option.some.injEq] at hc'
    exact .inl hc'.symm
  · rw [QueryCache.cacheQuery_of_ne _ _ h] at hc'
    exact .inr ⟨c', hc'⟩

theorem cfV_cacheQuery_subset (st : RS St Blk) (t : St × Blk) (u : St) :
    cfV (st.1.cacheQuery t u, st.2) ⊆ insert t.1 (cfV st) := by
  rintro v ⟨b, hb⟩
  by_cases h : (v, b) = t
  · subst h
    exact .inl rfl
  · rw [QueryCache.cacheQuery_of_ne _ _ h] at hb
    exact .inr ⟨b, hb⟩

theorem nV_draw_le (st : RS St Blk) (c : Empty ⊕ Nd Blk) (u : St) :
    nV (st.1, st.2.cacheQuery c u) ≤ nV st + 1 := by
  unfold nV
  have h1 := (Set.ncard_le_ncard (labV_cacheQuery_subset st c u) (Set.toFinite _)).trans
    (Set.ncard_insert_le u (labV st))
  have h2 : cfV (st.1, st.2.cacheQuery c u) = cfV st := rfl
  rw [h2]
  omega

theorem nV_ro_le (st : RS St Blk) (t : St × Blk) (u : St) :
    nV (st.1.cacheQuery t u, st.2) ≤ nV st + 1 := by
  unfold nV
  have h1 := (Set.ncard_le_ncard (cfV_cacheQuery_subset st t u) (Set.toFinite _)).trans
    (Set.ncard_insert_le t.1 (cfV st))
  have h2 : labV (st.1.cacheQuery t u, st.2) = labV st := rfl
  rw [h2]
  omega

end BadSets

/-! ## `Bad` of the Merkle–Damgård graph, both directions -/

section BadChar

variable (IV : St)

theorem childVals_cons (st : RS St Blk) (b p : Blk) (ps : List Blk) {v : St}
    (h : st.2 (.inr (p, ps)) = some v) :
    (mdG (Blk := Blk) IV).childVals st (b, p :: ps) = some [v] := by
  simp [LGraph.childVals, mdG, mdCh, h]

theorem childVals_nil (st : RS St Blk) (b : Blk) :
    (mdG (Blk := Blk) IV).childVals st (b, []) = some [] :=
  (mdG (Blk := Blk) IV).childVals_of_ch_nil rfl

theorem ptColl_of_eq [Nonempty Blk] {st : RS St Blk} {k k' : Nd Blk} {v : St} (hne : k ≠ k')
    (h : st.2 (.inr k) = some v) (h' : st.2 (.inr k') = some v) :
    (mdG (Blk := Blk) IV).PtColl st := by
  obtain ⟨b⟩ := ‹Nonempty Blk›
  obtain ⟨p, ps⟩ := k
  obtain ⟨p', ps'⟩ := k'
  refine ⟨(b, p :: ps), (b, p' :: ps'), [v], [v], childVals_cons IV st b p ps h,
    childVals_cons IV st b p' ps' h', rfl, ?_⟩
  intro he
  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at he
  exact hne (by rw [he.1, he.2])

theorem ptColl_of_IV [Nonempty Blk] {st : RS St Blk} {k : Nd Blk} (h : st.2 (.inr k) = some IV) :
    (mdG (Blk := Blk) IV).PtColl st := by
  obtain ⟨b⟩ := ‹Nonempty Blk›
  obtain ⟨p, ps⟩ := k
  refine ⟨(b, p :: ps), (b, []), [IV], [], childVals_cons IV st b p ps h, childVals_nil IV st b,
    rfl, ?_⟩
  simp

theorem conflict_of_lab {st : RS St Blk} {k : Nd Blk} {v : St} {b : Blk}
    (h : st.2 (.inr k) = some v) (hc : (st.1 (v, b)).isSome) :
    (mdG (Blk := Blk) IV).Conflict st :=
  ⟨(b, k.1 :: k.2), [v], childVals_cons IV st b k.1 k.2 h, hc⟩

theorem conflict_of_IV {st : RS St Blk} {b : Blk} (hc : (st.1 (IV, b)).isSome) :
    (mdG (Blk := Blk) IV).Conflict st :=
  ⟨(b, []), [], childVals_nil IV st b, hc⟩

variable [DecidableEq St] [DecidableEq Blk]

/-- **A fresh label off the bad set creates no `Bad`.** -/
theorem not_bad_draw [Nonempty Blk] {st : RS St Blk} (hb : ¬ (mdG (Blk := Blk) IV).Bad st)
    (k : Nd Blk) {u : St} (hu : u ∉ labV st) (hIV : u ≠ IV) (hc : u ∉ cfV st) :
    ¬ (mdG (Blk := Blk) IV).Bad (st.1, st.2.cacheQuery (.inr k) u) := by
  have hlab : ∀ k', k' ≠ k → (st.2.cacheQuery (.inr k) u) (.inr k') = st.2 (.inr k') :=
    fun k' hk ↦ QueryCache.cacheQuery_of_ne _ _ fun e ↦ hk (Sum.inr_injective e)
  have hself : (st.2.cacheQuery (.inr k) u) (.inr k) = some u := QueryCache.cacheQuery_self _ _ _
  rintro (h | h)
  · rcases conflict_imp IV h with ⟨k', v, b, hv, hcb⟩ | ⟨b, hcb⟩
    · by_cases hkk : k' = k
      · subst hkk
        rw [hself, Option.some.injEq] at hv
        subst hv
        exact hc ⟨b, hcb⟩
      · rw [hlab k' hkk] at hv
        exact hb (.inl (conflict_of_lab IV hv hcb))
    · exact hb (.inl (conflict_of_IV IV hcb))
  · rcases ptColl_imp IV h with ⟨k1, k2, v, hne, h1, h2⟩ | ⟨k1, h1⟩
    · by_cases hk1 : k1 = k
      · subst hk1
        rw [hself, Option.some.injEq] at h1
        subst h1
        rw [hlab k2 (Ne.symm hne)] at h2
        exact hu ⟨_, h2⟩
      · rw [hlab k1 hk1] at h1
        by_cases hk2 : k2 = k
        · subst hk2
          rw [hself, Option.some.injEq] at h2
          subst h2
          exact hu ⟨_, h1⟩
        · rw [hlab k2 hk2] at h2
          exact hb (.inr (ptColl_of_eq IV hne h1 h2))
    · by_cases hk1 : k1 = k
      · subst hk1
        rw [hself, Option.some.injEq] at h1
        exact hIV h1
      · rw [hlab k1 hk1] at h1
        exact hb (.inr (ptColl_of_IV IV h1))

/-- **A public cell cached off the node points creates no `Bad`.** -/
theorem not_bad_ro {st : RS St Blk} (hb : ¬ (mdG (Blk := Blk) IV).Bad st) {t : St × Blk}
    (ht : ¬∃ k vs, (mdG (Blk := Blk) IV).childVals st k = some vs ∧
      (mdG (Blk := Blk) IV).pt k vs = t) (u : St) :
    ¬ (mdG (Blk := Blk) IV).Bad (st.1.cacheQuery t u, st.2) := by
  rintro (h | h)
  · rcases conflict_imp IV h with ⟨k', v, b, hv, hcb⟩ | ⟨b, hcb⟩
    · by_cases hvb : (v, b) = t
      · exact ht ⟨(b, k'.1 :: k'.2), [v], childVals_cons IV st b k'.1 k'.2 hv, hvb⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hvb] at hcb
        exact hb (.inl (conflict_of_lab IV hv hcb))
    · by_cases hvb : (IV, b) = t
      · exact ht ⟨(b, []), [], childVals_nil IV st b, hvb⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hvb] at hcb
        exact hb (.inl (conflict_of_IV IV hcb))
  · exact hb (.inr h)

end BadChar

/-! ## One draw -/

section Draw

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] [Nonempty Blk]
  (IV : St)

theorem prEvent_mem_le (A : Set St) :
    Pr{let u ← ($ᵗ St : ProbComp St)}[u ∈ A] ≤ (A.ncard : ℝ≥0∞) / Fintype.card St := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  refine ENNReal.div_le_div_right ?_ _
  have : (Finset.univ.filter fun u : St ↦ u ∈ A) = A.toFinset := by ext; simp
  rw [this, ← Set.ncard_eq_toFinset_card']

/-- **One draw fires `Bad` with probability at most `(nV + 1)/|St|`.** -/
theorem prEvent_draw_bad {st : RS St Blk} (hb : ¬ (mdG (Blk := Blk) IV).Bad st)
    (c : Empty ⊕ Nd Blk) :
    Pr{let z ← (RelabelState.drawCell c).run st}[(mdG (Blk := Blk) IV).Bad z.2] ≤
      ((nV st + 1 : ℕ) : ℝ≥0∞) / Fintype.card St := by
  classical
  rcases c with x | k
  · exact x.elim
  cases hk : st.2 (.inr k) with
  | some v =>
    rw [RelabelState.drawCell_run_of_cell_eq_some hk, prEvent_pure]
    simp [hb]
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none hk, prEvent_map]
    refine (prEvent_mono _ _ (fun u ↦ u ∈ labV st ∪ {IV} ∪ cfV st) fun u hu ↦ ?_).trans
      ((prEvent_mem_le _).trans (ENNReal.div_le_div_right ?_ _))
    · by_contra hn
      simp only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff, not_or] at hn
      exact not_bad_draw IV hb k hn.1.2 hn.1.1 hn.2 hu
    · have h1 := Set.ncard_union_le (labV st ∪ {IV}) (cfV st)
      have h2 := Set.ncard_union_le (labV st) {IV}
      rw [Set.ncard_singleton] at h2
      unfold nV
      exact_mod_cast (h1.trans (by omega))

theorem nV_le_of_mem_support_drawCell {st : RS St Blk} {c : Empty ⊕ Nd Blk} {z}
    (hz : z ∈ support ((RelabelState.drawCell c).run st)) : nV z.2 ≤ nV st + 1 := by
  rw [RelabelState.drawCell_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  show nV (st.1, w.2) ≤ _
  rw [QueryImpl.withCaching_run_eq_cacheQuery _ hw]
  exact nV_draw_le st c w.1

/-- The expected hazard after one draw, with a pending charge on a fixed second component. -/
theorem ex_hz_draw {γ : Type} {st : RS St Blk} (hb : ¬ (mdG (Blk := Blk) IV).Bad st)
    (c : Empty ⊕ Nd Blk) (l : γ) (Ψ : RS St Blk × γ → ℝ≥0∞) (hΨ : ∀ st', Ψ (st', l) = Ψ (st, l)) :
    ex ((RelabelState.drawCell c).run st)
        (fun w ↦ hz (fun s : RS St Blk × γ ↦ (mdG (Blk := Blk) IV).Bad s.1) Ψ (w.2, l)) ≤
      ((nV st + 1 : ℕ) : ℝ≥0∞) / Fintype.card St + Ψ (st, l) := by
  have hpt : ∀ w : St × RS St Blk,
      hz (fun s : RS St Blk × γ ↦ (mdG (Blk := Blk) IV).Bad s.1) Ψ (w.2, l) ≤
        propInd ((mdG (Blk := Blk) IV).Bad w.2) + Ψ (st, l) := by
    intro w
    rw [← hΨ w.2]
    exact hz_le_propInd_add _ Ψ (w.2, l)
  refine (ex_mono _ hpt).trans ?_
  rw [ex_add, ex_const, ← prEvent_eq_ex]
  exact add_le_add (prEvent_draw_bad IV hb c) le_rfl

end Draw

/-! ## The end fill -/

section EndFill

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] [Nonempty Blk]
  (IV : St)

theorem qb_queryAll : ∀ (l : List (Empty ⊕ Nd Blk)),
    IsQueryBoundP ((((Empty ⊕ Nd Blk) →ₒ St)).queryAll l) (fun _ ↦ True) l.length
  | [] => by simp
  | c :: l => by
    rw [OracleSpec.queryAll_cons]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨.inr (by simp), fun _ ↦ ?_⟩
    simpa using qb_queryAll l

/-- **The end fill fires `Bad` with probability at most `#pending · Q/|St|`** under the cap. -/
theorem prEvent_endFill_bad (Q : ℕ) (st : RS St Blk) (l : List (Empty ⊕ Nd Blk))
    (hb : ¬ (mdG (Blk := Blk) IV).Bad st) (hQ : nV st + l.length ≤ Q) :
    Pr{let st' ← RelabelState.endFill (st, l)}[(mdG (Blk := Blk) IV).Bad st'] ≤
      l.length * ((Q : ℝ≥0∞) / Fintype.card St) := by
  rw [RelabelState.endFill_eq_simulateQ_cellImpl, prEvent_map]
  refine (prEvent_le_ex_hz _ (fun z : Unit × RS St Blk ↦ (mdG (Blk := Blk) IV).Bad z.2)
    (fun _ ↦ 0)).trans ?_
  have h := ex_hz_le_of_step_cap (RelabelState.cellImpl (pub := Cell St Blk)) (fun _ ↦ True)
    (mdG (Blk := Blk) IV).Bad (fun _ ↦ 0) (fun _ ↦ True) ((Q : ℝ≥0∞) / Fintype.card St) nV Q
    (fun _ _ _ _ _ ↦ trivial)
    (fun (t : Empty ⊕ Nd Blk) (s : RS St Blk) _ hs z hz ↦ hs.mono _
      (RelabelState.le_and_cell_eq_of_mem_support_drawCell (c := t) hz).1)
    (fun (t : Empty ⊕ Nd Blk) (s : RS St Blk) _ (z : St × RS St Blk) hz ↦ by
      simpa using nV_le_of_mem_support_drawCell (c := t) hz)
    (fun t s _ hs hlt ↦ by
      have h1 := ex_hz_draw IV hs t () (fun _ ↦ 0) (fun _ ↦ rfl)
      simp only [add_zero, ite_true, zero_add] at h1 ⊢
      refine le_trans ?_ (h1.trans (ENNReal.div_le_div_right ?_ _))
      · exact le_of_eq rfl
      · have := hlt trivial
        exact_mod_cast this)
    _ l.length (qb_queryAll l) st trivial hQ
  refine h.trans ?_
  rw [hz_of_not_P hb, zero_add]

end EndFill

/-! ## Query counts: the label program from the real program -/

section Count

variable (IV : St)

/-- The non-coin queries of the label interface. -/
def isNU : (WL St Blk).Domain → Bool
  | .inl (.inl (.inl _)) => false
  | _ => true

theorem qb_walkR_bind {β : Type} (f : St → OracleComp (unifSpec + Cell St Blk) β) :
    ∀ (bs : List Blk) (c : St) (n : ℕ), bs ≠ [] →
      IsQueryBoundP (walkR c bs >>= f) (fun i ↦ i.isRight = true) n →
      bs.length ≤ n ∧ ∀ v, IsQueryBoundP (f v) (fun i ↦ i.isRight = true) (n - bs.length)
  | [], _, _, h, _ => absurd rfl h
  | [b], c, n, _, h => by
    simp only [walkR, cR, bind_assoc, pure_bind] at h
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [Sum.isRight_inr, ite_true, not_true_eq_false, false_or] at h
    exact ⟨h.1, h.2⟩
  | b :: b' :: bs, c, n, _, h => by
    rw [walkR, cR, bind_assoc, isQueryBoundP_query_bind_iff] at h
    simp only [Sum.isRight_inr, ite_true, not_true_eq_false, false_or] at h
    obtain ⟨h0, h1⟩ := h
    have := fun u ↦ qb_walkR_bind f (b' :: bs) u (n - 1) (List.cons_ne_nil _ _) (h1 u)
    refine ⟨?_, fun v ↦ ?_⟩
    · obtain ⟨c'⟩ : Nonempty St := ⟨c⟩
      have := (this c').1
      simp only [List.length_cons] at this ⊢
      omega
    · obtain ⟨_, h2⟩ := this v
      have e : n - (b :: b' :: bs).length = n - 1 - (b' :: bs).length := by
        simp only [List.length_cons]; omega
      rw [e]
      exact h2 v

theorem qb_walkL_bind {β : Type} (g : St → OracleComp (WL St Blk) β) :
    ∀ (bs : List Blk) (rev : List Blk) (n : ℕ), bs ≠ [] → bs.length ≤ n →
      (∀ v, IsQueryBoundP (g v) (fun i ↦ isNU i = true) (n - bs.length)) →
      IsQueryBoundP (walkL IV rev bs >>= g) (fun i ↦ isNU i = true) n
  | [], _, _, h, _, _ => absurd rfl h
  | [b], rev, n, _, hl, hg => by
    rw [walkL.eq_2, rL, isQueryBoundP_query_bind_iff]
    have hp : isNU (Sum.inr (Sum.inr (b, rev)) : (WL St Blk).Domain) = true := rfl
    simp only [hp, ite_true]
    exact ⟨.inr (by simp only [List.length_cons, List.length_nil] at hl; omega), fun u ↦ hg u⟩
  | b :: b' :: bs, rev, n, _, hl, hg => by
    rw [walkL.eq_3, bind_assoc, tL, isQueryBoundP_query_bind_iff]
    have hp : isNU (Sum.inr (Sum.inl (Sum.inr (b, rev))) : (WL St Blk).Domain) = true := rfl
    simp only [hp, ite_true]
    refine ⟨.inr (by simp only [List.length_cons] at hl; omega), fun _ ↦ ?_⟩
    refine qb_walkL_bind g (b' :: bs) (b :: rev) (n - 1) (List.cons_ne_nil _ _)
      (by simp only [List.length_cons] at hl ⊢; omega) fun v ↦ ?_
    have e : n - 1 - (b' :: bs).length = n - (b :: b' :: bs).length := by
      simp only [List.length_cons]; omega
    rw [e]
    exact hg v

/-- **The label program makes at most as many non-coin queries as the real program makes
compression queries.** -/
theorem qb_labI {α : Type} (X : OracleComp (OSp St Blk) α) : ∀ n,
    IsQueryBoundP (simulateQ (cellsR IV) X) (fun i ↦ i.isRight = true) n →
      IsQueryBoundP (simulateQ (labI IV) X) (fun i ↦ isNU i = true) n := by
  induction X using OracleComp.inductionOn with
  | pure x => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro n h
    rw [simulateQ_query_bind] at h ⊢
    simp only [OracleQuery.input_query, monadLift_self] at h ⊢
    rcases t with (m | q) | bs
    · simp only [cellsR] at h
      simp only [labI]
      rw [isQueryBoundP_query_bind_iff] at h ⊢
      have hp : isNU (Sum.inl (Sum.inl (Sum.inl m)) : (WL St Blk).Domain) = false := rfl
      simp only [Sum.isRight_inl, hp, Bool.false_eq_true, ite_false] at h ⊢
      exact ⟨.inl (by simp), fun u ↦ ih u n (h.2 u)⟩
    · simp only [cellsR] at h
      simp only [labI, cL]
      rw [isQueryBoundP_query_bind_iff] at h ⊢
      have hp : isNU (Sum.inl (Sum.inl (Sum.inr q)) : (WL St Blk).Domain) = true := rfl
      simp only [Sum.isRight_inr, hp, ite_true] at h ⊢
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · simp only [cellsR] at h
      simp only [labI]
      cases bs with
      | nil =>
        simp only [walkR, walkL, pure_bind] at h ⊢
        exact ih _ n h
      | cons b bs =>
        obtain ⟨hl, hv⟩ := qb_walkR_bind _ (b :: bs) IV n (List.cons_ne_nil _ _) h
        exact qb_walkL_bind IV _ (b :: bs) [] n (List.cons_ne_nil _ _) hl fun v ↦ ih v _ (hv v)

end Count

/-! ## The deferred game -/

section Deferred

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] [Nonempty Blk]
  (IV : St)

/-- The size of a deferred state: drawn values, cached chaining inputs, pending touches. -/
noncomputable def dSize (s : RS St Blk × List (Empty ⊕ Nd Blk)) : ℕ := nV s.1 + s.2.length

theorem dSize_step (t : (WL St Blk).Domain) (s : RS St Blk × List (Empty ⊕ Nd Blk))
    (z) (hz : z ∈ support (((mdG (Blk := Blk) IV).deferredImpl t).run s)) :
    dSize z.2 ≤ dSize s + (if isNU t = true then 1 else 0) := by
  classical
  unfold dSize
  rcases t with ((n | t) | x) | (c | k)
  · rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_unif, Functor.map_map,
      support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact Nat.le_add_right _ _
  · rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_pub, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [isNU, ite_true]
    split_ifs at hw with h
    · rw [support_map] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      have := nV_le_of_mem_support_drawCell hy
      simp only [Prod.map_snd, id_eq]
      omega
    · rw [support_map] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      show nV (y.2, s.1.2) + s.2.length ≤ _
      rw [QueryImpl.withCaching_run_eq_cacheQuery _ hy]
      have := nV_ro_le s.1 t y.1
      omega
  · exact x.elim
  · rw [LGraph.deferredImpl_run_touch, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [isNU, ite_true, List.length_append, List.length_singleton]
    omega
  · rw [LGraph.deferredImpl_run_read, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have := nV_le_of_mem_support_drawCell hw
    simp only [isNU, ite_true]
    omega

/-- The pending charge of the deferred touches. -/
noncomputable def pend (ε : ℝ≥0∞) (s : RS St Blk × List (Empty ⊕ Nd Blk)) : ℝ≥0∞ :=
  s.2.length * ε

theorem dStep (Q : ℕ) (t : (WL St Blk).Domain) (s : RS St Blk × List (Empty ⊕ Nd Blk))
    (hb : ¬ (mdG (Blk := Blk) IV).Bad s.1) (hlt : isNU t = true → dSize s < Q) :
    ex (((mdG (Blk := Blk) IV).deferredImpl t).run s)
        (fun z ↦ hz (fun s : RS St Blk × List (Empty ⊕ Nd Blk) ↦ (mdG (Blk := Blk) IV).Bad s.1)
          (pend ((Q : ℝ≥0∞) / Fintype.card St)) z.2) ≤
      pend ((Q : ℝ≥0∞) / Fintype.card St) s +
        (if isNU t = true then (Q : ℝ≥0∞) / Fintype.card St else 0) := by
  classical
  set ε := (Q : ℝ≥0∞) / Fintype.card St
  set P := fun s : RS St Blk × List (Empty ⊕ Nd Blk) ↦ (mdG (Blk := Blk) IV).Bad s.1
  have hcap : isNU t = true → ((nV s.1 + 1 : ℕ) : ℝ≥0∞) / Fintype.card St ≤ ε := fun h ↦
    ENNReal.div_le_div_right (by have := hlt h; unfold dSize at this; exact_mod_cast (by omega)) _
  have hdraw : ∀ c, isNU t = true →
      ex ((fun z ↦ (z.1, (z.2, s.2))) <$> (RelabelState.drawCell c).run s.1)
        (fun z ↦ hz P (pend ε) z.2) ≤ pend ε s + ε := by
    intro c h
    rw [ex_map]
    refine (ex_hz_draw IV hb c s.2 (pend ε) fun _ ↦ rfl).trans ?_
    rw [add_comm]
    exact add_le_add le_rfl (hcap h)
  rcases t with ((n | t) | x) | (c | k)
  · rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_unif, Functor.map_map, ex_map]
    simp only [Function.comp_def, isNU, Bool.false_eq_true, ite_false, add_zero]
    rw [ex_const, hz_of_not_P (P := P) (s := (s.1, s.2)) hb]
  · rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_pub]
    simp only [isNU, ite_true]
    split_ifs with h
    · rw [Functor.map_map, ex_map]
      have := hdraw (.inr h.choose) rfl
      rw [ex_map] at this
      exact this
    · rw [Functor.map_map, ex_map]
      refine le_trans (ex_mono_of_support _ (g := fun _ ↦ pend ε s) fun y hy ↦ ?_) ?_
      · simp only [Function.comp_apply]
        rw [hz_of_not_P]
        · rfl
        · show ¬ (mdG (Blk := Blk) IV).Bad (y.2, s.1.2)
          rw [QueryImpl.withCaching_run_eq_cacheQuery _ hy]
          exact not_bad_ro IV hb h y.1
      · rw [ex_const]; exact le_self_add
  · exact x.elim
  · rw [LGraph.deferredImpl_run_touch, ex_pure]
    show hz P (pend ε) (s.1, s.2 ++ [c]) ≤ _
    rw [hz_of_not_P (P := P) (s := (s.1, s.2 ++ [c])) hb]
    simp only [isNU, ite_true, pend, List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul, le_refl]
  · rw [LGraph.deferredImpl_run_read]
    simp only [isNU, ite_true]
    exact hdraw _ rfl

/-- **The bad event of the deferred game with its end fill.**  With `n` non-coin label-program
queries and a cap `Q ≥ n`: `Pr[Bad] ≤ n · Q/|St|`. -/
theorem prBad_defRun_le {α : Type} (X : OracleComp (OSp St Blk) α) (Q n : ℕ)
    (hn : IsQueryBoundP (simulateQ (labI IV) X) (fun i ↦ isNU i = true) n) (hnQ : n ≤ Q) :
    Pr{let z ← (simulateQ (mdG (Blk := Blk) IV).deferredImpl (simulateQ (labI IV) X)).run
        ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[(mdG (Blk := Blk) IV).Bad st] ≤
      n * ((Q : ℝ≥0∞) / Fintype.card St) := by
  set ε := (Q : ℝ≥0∞) / Fintype.card St
  set G := mdG (Blk := Blk) IV
  set P := fun s : RS St Blk × List (Empty ⊕ Nd Blk) ↦ G.Bad s.1
  set A := (simulateQ G.deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
  have hsupp := size_le_of_mem_support_run G.deferredImpl (fun i ↦ isNU i = true) dSize
    (dSize_step IV) _ n hn ((∅, ∅), [])
  have e0 : dSize (((∅, ∅), []) : RS St Blk × List (Empty ⊕ Nd Blk)) = 0 := by
    simp [dSize, nV_empty]
  have h1 : Pr{let z ← A; let st ← RelabelState.endFill z.2}[G.Bad st] =
      ex A fun z ↦ Pr{let st ← RelabelState.endFill z.2}[G.Bad st] := by
    have h0 : Pr{let z ← A; let st ← RelabelState.endFill z.2}[G.Bad st] =
        Pr{let st ← A >>= fun z ↦ RelabelState.endFill z.2}[G.Bad st] := by
      simp only [prEvent_norm]
    rw [h0, prEvent_eq_ex, ex_bind]
    refine congrArg (ex A) (funext fun z ↦ ?_)
    rw [prEvent_eq_ex]
  rw [h1]
  refine (ex_mono_of_support _ (g := fun z ↦ hz P (pend ε) z.2) fun z hz' ↦ ?_).trans ?_
  · have hs := hsupp z hz'
    rw [e0, zero_add] at hs
    by_cases hb : G.Bad z.2.1
    · rw [hz_of_P (P := P) hb]; exact prEvent_le_one _
    · rw [hz_of_not_P (P := P) hb]
      exact prEvent_endFill_bad IV Q z.2.1 z.2.2 hb (by unfold dSize at hs; omega)
  · have h := ex_hz_le_of_step_cap G.deferredImpl (fun _ ↦ True) P (pend ε)
      (fun i ↦ isNU i = true) ε dSize Q (fun _ _ _ _ _ ↦ trivial)
      (fun t s _ hs z hz ↦ hs.mono _ (G.le_of_mem_support_deferredImpl hz))
      (fun t s _ z hz ↦ dSize_step IV t s z hz)
      (fun t s _ hs hlt ↦ dStep IV Q t s hs hlt)
      _ n hn ((∅, ∅), []) trivial (by rw [e0]; omega)
    refine h.trans ?_
    rw [hz_of_not_P (P := P) G.not_bad_empty]
    simp [pend]

end Deferred

end MD

/-! ## `BadSuf`, `BadEuf` -/

namespace Rom

open SLHDSA SLHDSA.Security Ideal.Realize Ideal.Realize.Prf

instance : Nonempty Blk := inferInstance

theorem card_St : (Fintype.card St : ℝ≥0∞) = 2 ^ 256 := by
  rw [card_bytes]; norm_num

theorem two_mul_bound (Q : ℕ) :
    2 * ((Q : ℝ≥0∞) * ((Q : ℝ≥0∞) / Fintype.card St)) ≤ (((Q + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 255 := by
  rw [card_St, ← mul_div_assoc, ← mul_div_assoc]
  have h : (2 : ℝ≥0∞) ^ 256 = 2 * 2 ^ 255 := by rw [← pow_succ']
  rw [h, ENNReal.mul_div_mul_left _ _ two_ne_zero ofNat_ne_top]
  refine ENNReal.div_le_div_right ?_ _
  have : Q * Q ≤ (Q + 1) ^ 2 := by nlinarith
  exact_mod_cast this

theorem badRun_le (X : OracleComp OS Bool) (Q : ℕ)
    (hX : IsQueryBoundP (simulateQ (MD.cellsR IV128) X) (fun i ↦ i.isRight = true) Q) :
    2 * Pr{let w ← defRun X}[Gs.Bad w.2] ≤ (((Q + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 255 := by
  rw [← defRun_prEvent X (fun _ st ↦ Gs.Bad st)]
  refine le_trans ?_ (two_mul_bound Q)
  gcongr
  exact MD.prBad_defRun_le IV128 X Q Q (MD.qb_labI IV128 X Q hX) le_rfl

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))

/-- **`BadSuf`, proved.** -/
theorem badSuf : BadSuf := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  have h := progS_comp S oR ($ᵗ (Bytes 16)) hqf hqs hlong hout
  rw [h1_suf] at h
  have h' := h.mono (Nat.add_le_add_right (qPrf_le_QcAll qf qs ℓ) _)
  exact badRun_le _ (QAll qf qs ℓ) h'

/-- **`BadEuf`, proved.** -/
theorem badEuf : BadEuf := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  have h := progE_comp S oR ($ᵗ (Bytes 16)) hqf hqs hlong hout
  rw [h1_euf] at h
  have h' := h.mono (Nat.add_le_add_right (qPrf_le_QcAll qf qs ℓ) _)
  exact badRun_le _ (QAll qf qs ℓ) h'

end Rom

end Ideal.Direct

#print axioms Ideal.Direct.size_le_of_mem_support_run
#print axioms Ideal.Direct.MD.not_bad_draw
#print axioms Ideal.Direct.MD.not_bad_ro
#print axioms Ideal.Direct.MD.prEvent_draw_bad
#print axioms Ideal.Direct.MD.prEvent_endFill_bad
#print axioms Ideal.Direct.MD.qb_labI
#print axioms Ideal.Direct.MD.prBad_defRun_le
#print axioms Ideal.Direct.Rom.badSuf
#print axioms Ideal.Direct.Rom.badEuf
