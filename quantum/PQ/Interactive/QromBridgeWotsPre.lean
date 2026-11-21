import PQ.Interactive.QromBridgeUnif
import PQ.QROM.PreGiven
import VCVio.OracleComp.EvalDist.Sum

/-!
# The WOTS-chain PRE bridge, game side: generic part

Generic (no SLH-DSA) facts about VCVio's SM-DT-PRE game (`SM_DT_PRE_oracles`) with a quantum
second phase.

* `prePlantO P pk ans rec ce`: the *planted* oracles: an accepted challenge query at tweak `t`
  answers `ans t` and records `(t, rec t)` (no sampling); collection answers by `ce`.
* `pre_run_plant` (**lazy sampling**): the selection phase against the real oracles (fresh uniform
  `x` per accepted challenge) has the output distribution of the planted phase with
  `rec := xs`, `ans t := th (t, emb (xs t))`, averaged over a uniform `xs : Tw → M'`.
* `prePlant_relabel`: the probability that a planted run ends in the state
  `(s, tws.map (t ↦ (t, rec t)), C)` depends on `ans` only at the tweaks `tws`, on the collection
  only at the tweaks outside `tws`, and not at all on `rec`.
* **`pre_row_avg_le`**: if the attacked hash at the seed `pk` is a uniformly random row
  `R : Tw × M' → Y` (read through `emb`), the collection at tweak `t` reads only `R (t, ·)`, and the
  second phase is described for every first-phase state by a `q`-query hybrid model over the row,
  then the row-average of the game's winning weight at `pk` is at most
  `(2q+1)² (1/|Y| + 1/|M'|)` (`PQ.QROM.pre_embedded_obs_weighted_le`).  No uniformity of the seed.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory TweakableHash

set_option linter.unusedSectionVars false

namespace PQ.Interactive


/-! ### Generic helpers (own copies; `PQ/Interactive/QromBridgeTcr.lean` has the same facts) -/

section helpers

variable {W : Type} [Fintype W] {α β γ : Type}

/-- The output masses of a probabilistic computation sum to at most one. -/
lemma wq_tsum_prob_le_one (oa : ProbComp γ) : ∑' x, prob oa (· = x) ≤ 1 :=
  tsum_prEvent_le_one oa

/-- Classical sampling in front of a closed machine, any output type. -/
lemma wq_qWeight_liftU_bind_tsum (p : α → Prop) [DecidablePred p] (oa : ProbComp γ)
    (f : γ → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (liftU oa >>= f) ρ = ∑' x, prob oa (· = x) * qWeight p (f x) ρ := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    classical
    rw [liftU_pure, pure_bind]
    simp only [prob_pure, ite_mul, one_mul, zero_mul, @eq_comm _ a]
    rw [tsum_ite_eq]
  | query_bind n k ih =>
    rw [liftU_query_bind, bind_assoc, qWeight_unif_bind]
    simp only [ih, prob_unif_query_bind]
    simp only [mul_assoc, ENNReal.tsum_mul_left, Finset.sum_mul]
    rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]

/-- A deterministic Boolean post-processing is an event. -/
lemma wq_qWeight_bind_pure_decide (E : α → Prop) [DecidablePred E] (X : Closed W α)
    (ρ : Matrix W W ℂ) :
    qWeight (· = true) (X >>= fun a ↦ pure (decide (E a))) ρ = qWeight E X ρ := by
  rw [bind_pure_comp, qWeight_map]
  have e : (fun a ↦ decide (E a) = true) = E := funext fun a ↦ propext (by simp)
  simp only [e]

/-- An output outside the support has probability zero. -/
lemma wq_prob_eq_zero_of_forall_ne {S : Type} (mx : ProbComp S) (z : S)
    (h : ∀ w ∈ support mx, w ≠ z) : prob mx (· = z) = 0 :=
  prEvent_eq_zero_of_not_mem_support mx fun hz ↦ h z hz rfl

/-- Patching along the identity embedding is the row itself. -/
theorem wq_patch_refl_eq {Tw M Y : Type} [Fintype Tw] [DecidableEq Tw] [Fintype M] [DecidableEq M]
    (F : Tw × M → Y) (R : Tw × M → Y) :
    PQ.QROM.patch F (Function.Embedding.refl (Tw × M)) R = R := by
  funext z
  exact PQ.QROM.patch_apply F (Function.Embedding.refl (Tw × M)) R z

end helpers

/-- `τ` extends `σ`: the challenge history grows by entries fresh for both histories of `σ`; the
collection list grows. -/
def PreExt {Tw M' : Type} (σ τ : TweakableHash.SM_DT_PRE_State Tw M') : Prop :=
  ∃ s, τ.1 = σ.1 ++ s ∧ (∀ e ∈ s, e.1 ∉ σ.1.map Prod.fst ∧ e.1 ∉ σ.2) ∧ σ.2 ⊆ τ.2

theorem preExt_refl {Tw M' : Type} (σ : TweakableHash.SM_DT_PRE_State Tw M') : PreExt σ σ :=
  ⟨[], by simp, by simp, fun _ h ↦ h⟩

theorem preExt_trans {Tw M' : Type} {σ τ υ : TweakableHash.SM_DT_PRE_State Tw M'}
    (h₁ : PreExt σ τ) (h₂ : PreExt τ υ) : PreExt σ υ := by
  obtain ⟨s, hs, hsf, hsc⟩ := h₁
  obtain ⟨s', hs', hsf', hsc'⟩ := h₂
  refine ⟨s ++ s', by rw [hs', hs, List.append_assoc], ?_, fun x hx ↦ hsc' (hsc hx)⟩
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hsf e he
  · refine ⟨fun hm ↦ (hsf' e he).1 ?_, fun hm ↦ (hsf' e he).2 (hsc hm)⟩
    rw [hs, List.map_append]
    exact List.mem_append_left _ hm

/-- Congruence of the probability of events under a common first draw (events may differ). -/
lemma wq_prob_bind_congr {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β) (E E' : β → Prop)
    (h : ∀ x, prob (f x) E = prob (g x) E') : prob (mx >>= f) E = prob (mx >>= g) E' := by
  unfold prob at h ⊢
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  simp only [h]

/-- Probability of an event after a first draw, as a sum over the draw. -/
lemma wq_prob_bind_tsum {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (E : β → Prop) :
    prob (mx >>= f) E = ∑' x, prob mx (· = x) * prob (f x) E :=
  prEvent_bind_eq_tsum mx f E

section wpre

variable {ι PkSeed Tw M M' Y : Type} [DecidableEq Tw]

/-- `P` with the evaluations of the attacked hash and of the collection replaced. -/
abbrev preWithEval (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (th : PkSeed → Tw → M → Y)
    (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) : SM_DT_PRE_Problem ι PkSeed Tw M M' Y where
  th := ⟨P.th.seedGen, th⟩
  emb := P.emb
  emb_injective := P.emb_injective
  thColl := ⟨P.thColl.Msg, ce⟩
  numTargets := P.numTargets

/-- Interface of the selection phase. -/
abbrev PreSpecG (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) :=
  unifSpec + (SM_DT_PRE_challengeSpec Tw Y + collectionSpec P.thColl)

/-- The planted challenge oracle: an accepted query at `t` answers `ans t` and records
`(t, rec t)`; the acceptance test is that of `SM_DT_PRE_challengeOracle`. -/
noncomputable def prePlantChal (N : ℕ) (ans : Tw → Y) (rec : Tw → M') :
    QueryImpl (SM_DT_PRE_challengeSpec Tw Y) (StateT (SM_DT_PRE_State Tw M') ProbComp) :=
  fun t => do
    let (qsChal, twsColl) ← get
    if N ≤ qsChal.length ∨ ¬ TweakFresh Prod.fst qsChal twsColl t then
      return none
    else
      set (qsChal ++ [(t, rec t)], twsColl)
      return some (ans t)

/-- The planted oracles of the SM-PRE game (collection evaluated by `ce`). -/
noncomputable def prePlantO (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (ans : Tw → Y) (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) :
    QueryImpl (PreSpecG P) (StateT (SM_DT_PRE_State Tw M') ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM_DT_PRE_State Tw M') ProbComp) +
    (prePlantChal P.numTargets ans rec +
      collectionOracle (Q := Tw × M') Prod.fst
        (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y) pk)

/-! ### Step equations -/

theorem prePlant_unif (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) (n : ℕ)
    (σ : SM_DT_PRE_State Tw M') :
    (prePlantO P pk ans rec ce (.inl n)).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [prePlantO]

theorem preReal_unif [SampleableType M'] (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (n : ℕ) (σ : SM_DT_PRE_State Tw M') :
    (SM_DT_PRE_oracles P pk (.inl n)).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [SM_DT_PRE_oracles]

theorem prePlant_chal_rej (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) (t : Tw)
    (L : List (Tw × M')) (C : List Tw)
    (hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t) :
    (prePlantO P pk ans rec ce (.inr (.inl t))).run (L, C) = pure (none, (L, C)) := by
  change (prePlantChal P.numTargets ans rec t).run (L, C) = _
  simp [prePlantChal, hc]

theorem prePlant_chal_acc (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) (t : Tw)
    (L : List (Tw × M')) (C : List Tw)
    (hc : ¬ (P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t)) :
    (prePlantO P pk ans rec ce (.inr (.inl t))).run (L, C) =
      pure (some (ans t), (L ++ [(t, rec t)], C)) := by
  change (prePlantChal P.numTargets ans rec t).run (L, C) = _
  simp [prePlantChal, hc]

theorem preReal_chal_rej [SampleableType M'] (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y)
    (pk : PkSeed) (t : Tw) (L : List (Tw × M')) (C : List Tw)
    (hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t) :
    (SM_DT_PRE_oracles P pk (.inr (.inl t))).run (L, C) = pure (none, (L, C)) := by
  change (SM_DT_PRE_challengeOracle P pk t).run (L, C) = _
  simp [SM_DT_PRE_challengeOracle, hc]

theorem preReal_chal_acc [SampleableType M'] (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y)
    (pk : PkSeed) (t : Tw) (L : List (Tw × M')) (C : List Tw)
    (hc : ¬ (P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t)) :
    (SM_DT_PRE_oracles P pk (.inr (.inl t))).run (L, C) =
      (($ᵗ M' : ProbComp M') >>= fun x ↦
        pure (some (P.th.eval pk t (P.emb x)), (L ++ [(t, x)], C))) := by
  change (SM_DT_PRE_challengeOracle P pk t).run (L, C) = _
  simp [SM_DT_PRE_challengeOracle, hc]

theorem prePlant_coll (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    (q : (i : ι) × Tw × P.thColl.Msg i) (σ : SM_DT_PRE_State Tw M') :
    (prePlantO P pk ans rec ce (.inr (.inr q))).run σ =
      (collectionOracle (Q := Tw × M') Prod.fst
        (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y) pk q).run σ := rfl

theorem preReal_coll [SampleableType M'] (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (q : (i : ι) × Tw × P.thColl.Msg i) (σ : SM_DT_PRE_State Tw M') :
    (SM_DT_PRE_oracles P pk (.inr (.inr q))).run σ =
      (collectionOracle (Q := Tw × M') Prod.fst P.thColl pk q).run σ := rfl


/-! ### Reachable states of planted runs -/

/-- One planted step extends the state . -/
theorem prePlant_step_ext (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    (q : (PreSpecG P).Domain) (σ : SM_DT_PRE_State Tw M') :
    ∀ p ∈ support ((prePlantO P pk ans rec ce q).run σ), PreExt σ p.2 := by
  obtain ⟨L, C⟩ := σ
  rcases q with n | t | q
  · intro p hp
    rw [prePlant_unif] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact preExt_refl _
  · intro p hp
    by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
    · rw [prePlant_chal_rej P pk ans rec ce t L C hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact preExt_refl _
    · rw [prePlant_chal_acc P pk ans rec ce t L C hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp only [not_or, not_le, not_not] at hc
      obtain ⟨-, hres, hcoll⟩ := hc
      refine ⟨[(t, rec t)], rfl, ?_, fun _ h ↦ h⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      refine ⟨fun hm ↦ hres ?_, hcoll⟩
      obtain ⟨e', he', h'⟩ := List.mem_map.1 hm
      exact ⟨e', he', h'⟩
  · intro p hp
    rw [prePlant_coll] at hp
    by_cases hc : TweakReserved Prod.fst L q.2.1
    · rw [collectionOracle_run_of_challenge_clash
        (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact preExt_refl _
    · rw [collectionOracle_run_of_fresh
        (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨[], by simp, by simp, fun x hx ↦ List.mem_append_left _ hx⟩

/-- A planted run extends the state. -/
theorem prePlant_run_ext (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) {S : Type}
    (oa : OracleComp (PreSpecG P) S) (σ : SM_DT_PRE_State Tw M') :
    ∀ z ∈ support ((simulateQ (prePlantO P pk ans rec ce) oa).run σ), PreExt σ z.2 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact preExt_refl _
  | query_bind q k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff ..).mp hz
    exact preExt_trans (prePlant_step_ext P pk ans rec ce q σ p hp) (ih p.1 p.2 z hz)

/-! ### Invariance of planted runs -/

/-- A planted run does not read `ans`, `rec` at tweaks already in the challenge history. -/
theorem prePlant_congr_used (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (ans ans' : Tw → Y) (rec rec' : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    {S : Type} (oa : OracleComp (PreSpecG P) S) (L : List (Tw × M')) (C : List Tw)
    (h : ∀ t, t ∉ L.map Prod.fst → ans t = ans' t ∧ rec t = rec' t)
    (z : S × SM_DT_PRE_State Tw M') :
    prob ((simulateQ (prePlantO P pk ans rec ce) oa).run (L, C)) (· = z) =
      prob ((simulateQ (prePlantO P pk ans' rec' ce) oa).run (L, C)) (· = z) := by
  induction oa using OracleComp.inductionOn generalizing L C with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with n | t | q
    · rw [prePlant_unif, prePlant_unif, bind_map_left, bind_map_left]
      exact wq_prob_bind_congr _ _ _ _ _ fun u ↦ ih u L C h
    · by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
      · rw [prePlant_chal_rej P pk ans rec ce t L C hc, prePlant_chal_rej P pk ans' rec' ce t L C hc,
          pure_bind, pure_bind]
        exact ih _ L C h
      · rw [prePlant_chal_acc P pk ans rec ce t L C hc, prePlant_chal_acc P pk ans' rec' ce t L C hc,
          pure_bind, pure_bind]
        have ht : t ∉ L.map Prod.fst := by
          simp only [not_or, not_le, not_not] at hc
          obtain ⟨-, hres, -⟩ := hc
          intro hm
          obtain ⟨e', he', h'⟩ := List.mem_map.1 hm
          exact hres ⟨e', he', h'⟩
        obtain ⟨ha, hr⟩ := h t ht
        rw [ha, hr]
        refine ih _ _ C fun t' ht' ↦ h t' fun hm ↦ ht' ?_
        rw [List.map_append]
        exact List.mem_append_left _ hm
    · rw [prePlant_coll, prePlant_coll]
      by_cases hc : TweakReserved Prod.fst L q.2.1
      · rw [collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc,
          pure_bind, pure_bind]
        exact ih _ L C h
      · rw [collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc,
          pure_bind, pure_bind]
        exact ih _ L _ h

/-! ### Relabelling the records of a planted run -/

theorem wq_tweakReserved_map_pair (f : Tw → M') (Lt : List Tw) (t : Tw) :
    TweakReserved Prod.fst (Lt.map fun t ↦ (t, f t)) t ↔ t ∈ Lt := by
  simp [TweakReserved]

theorem wq_map_pair_inj (f : Tw → M') (Lt tws : List Tw) :
    (Lt.map fun t ↦ (t, f t)) = tws.map (fun t ↦ (t, f t)) ↔ Lt = tws := by
  constructor
  · intro h
    have := congrArg (List.map Prod.fst) h
    simp only [List.map_map, Function.comp_def, List.map_id'] at this
    exact this
  · rintro rfl
    rfl

theorem wq_tweakFresh_map_pair (f g : Tw → M') (Lt C : List Tw) (t : Tw) :
    TweakFresh Prod.fst (Lt.map fun t ↦ (t, f t)) C t ↔
      TweakFresh Prod.fst (Lt.map fun t ↦ (t, g t)) C t := by
  unfold TweakFresh
  rw [wq_tweakReserved_map_pair, wq_tweakReserved_map_pair]

/-- **Relabelling.**  The probability that a planted run ends with challenge history
`tws.map (t ↦ (t, rec t))` (and given state, collection list) is the same for `(ans₁, rec₁, ce₁)`
and `(ans₂, rec₂, ce₂)` when the answers agree on `tws` and the collections agree off `tws`. -/
theorem prePlant_relabel (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (ans₁ ans₂ : Tw → Y) (rec₁ rec₂ : Tw → M')
    (ce₁ ce₂ : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) {S : Type}
    (oa : OracleComp (PreSpecG P) S) (s : S) (tws Cf : List Tw)
    (hans : ∀ t ∈ tws, ans₁ t = ans₂ t) (hce : ∀ i t x, t ∉ tws → ce₁ i pk t x = ce₂ i pk t x)
    (Lt C : List Tw) :
    prob ((simulateQ (prePlantO P pk ans₁ rec₁ ce₁) oa).run (Lt.map fun t ↦ (t, rec₁ t), C))
        (· = (s, (tws.map fun t ↦ (t, rec₁ t), Cf))) =
      prob ((simulateQ (prePlantO P pk ans₂ rec₂ ce₂) oa).run (Lt.map fun t ↦ (t, rec₂ t), C))
        (· = (s, (tws.map fun t ↦ (t, rec₂ t), Cf))) := by
  classical
  induction oa using OracleComp.inductionOn generalizing Lt C with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, prob_pure]
    have e : ∀ f : Tw → M', ((x, (Lt.map fun t ↦ (t, f t), C)) =
        (s, (tws.map fun t ↦ (t, f t), Cf))) ↔ (x = s ∧ Lt = tws ∧ C = Cf) := by
      intro f
      simp only [Prod.mk.injEq, wq_map_pair_inj]
    simp only [e rec₁, e rec₂]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    -- zero: a reachable final history extends the current one
    have hzero : ∀ (ans : Tw → Y) (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
        (oa' : OracleComp (PreSpecG P) S) (L : List (Tw × M')) (C' : List Tw),
        (∀ (w : List (Tw × M')), PreExt (L, C') (s, (w, Cf)).2 → w = tws.map (fun t ↦ (t, rec t)) →
          False) →
        prob ((simulateQ (prePlantO P pk ans rec ce) oa').run (L, C'))
          (· = (s, (tws.map fun t ↦ (t, rec t), Cf))) = 0 := by
      intro ans rec ce oa' L C' hf
      refine wq_prob_eq_zero_of_forall_ne _ _ fun w hw hwz ↦ ?_
      have := prePlant_run_ext P pk ans rec ce oa' (L, C') w hw
      rw [hwz] at this
      exact hf _ this rfl
    rcases q with n | t | q
    · rw [prePlant_unif, prePlant_unif, bind_map_left, bind_map_left]
      exact wq_prob_bind_congr _ _ _ _ _ fun u ↦ ih u Lt C
    · have hlen : ∀ f : Tw → M', (Lt.map fun t ↦ (t, f t)).length = Lt.length := fun _ ↦
        List.length_map _
      by_cases hc : P.numTargets ≤ Lt.length ∨ ¬ TweakFresh Prod.fst (Lt.map fun t ↦ (t, rec₁ t)) C t
      · have hc2 : P.numTargets ≤ (Lt.map fun t ↦ (t, rec₂ t)).length ∨
            ¬ TweakFresh Prod.fst (Lt.map fun t ↦ (t, rec₂ t)) C t := by
          rw [hlen, ← wq_tweakFresh_map_pair rec₁]; exact hc
        rw [← hlen rec₁] at hc
        rw [prePlant_chal_rej P pk ans₁ rec₁ ce₁ t _ C hc,
          prePlant_chal_rej P pk ans₂ rec₂ ce₂ t _ C hc2, pure_bind, pure_bind]
        exact ih _ Lt C
      · have hc2 : ¬ (P.numTargets ≤ (Lt.map fun t ↦ (t, rec₂ t)).length ∨
            ¬ TweakFresh Prod.fst (Lt.map fun t ↦ (t, rec₂ t)) C t) := by
          rw [hlen, ← wq_tweakFresh_map_pair rec₁]; exact hc
        rw [← hlen rec₁] at hc
        rw [prePlant_chal_acc P pk ans₁ rec₁ ce₁ t _ C hc,
          prePlant_chal_acc P pk ans₂ rec₂ ce₂ t _ C hc2, pure_bind, pure_bind]
        have hm : ∀ f : Tw → M', (Lt.map fun t ↦ (t, f t)) ++ [(t, f t)] =
            (Lt ++ [t]).map fun t ↦ (t, f t) := fun f ↦ by simp
        rw [hm rec₁, hm rec₂]
        by_cases ht : t ∈ tws
        · rw [hans t ht]
          exact ih _ (Lt ++ [t]) C
        · have hz : ∀ (ans : Tw → Y) (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
              (u : Option Y), prob ((simulateQ (prePlantO P pk ans rec ce) (k u)).run
                ((Lt ++ [t]).map fun t ↦ (t, rec t), C))
                (· = (s, (tws.map fun t ↦ (t, rec t), Cf))) = 0 := by
            intro ans rec ce u
            refine hzero ans rec ce (k u) _ C fun w hext hw ↦ ?_
            obtain ⟨s', hs', -, -⟩ := hext
            have hmem : (t, rec t) ∈ w := by
              rw [show w = (s, (w, Cf)).2.1 from rfl, hs']
              simp
            rw [hw] at hmem
            obtain ⟨t', ht', he⟩ := List.mem_map.1 hmem
            have e' : t' = t := congrArg Prod.fst he
            exact ht (e' ▸ ht')
          rw [hz, hz]
    · rw [prePlant_coll, prePlant_coll]
      by_cases hc : TweakReserved Prod.fst (Lt.map fun t ↦ (t, rec₁ t)) q.2.1
      · have hc2 : TweakReserved Prod.fst (Lt.map fun t ↦ (t, rec₂ t)) q.2.1 := by
          rw [wq_tweakReserved_map_pair] at hc ⊢; exact hc
        rw [collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce₁⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc,
          collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce₂⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc2,
          pure_bind, pure_bind]
        exact ih _ Lt C
      · have hc2 : ¬ TweakReserved Prod.fst (Lt.map fun t ↦ (t, rec₂ t)) q.2.1 := by
          rw [wq_tweakReserved_map_pair] at hc ⊢; exact hc
        rw [collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce₁⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc,
          collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce₂⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc2,
          pure_bind, pure_bind]
        by_cases ht : q.2.1 ∈ tws
        · have hz : ∀ (ans : Tw → Y) (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
              (u : Option Y), prob ((simulateQ (prePlantO P pk ans rec ce) (k u)).run
                ((Lt.map fun t ↦ (t, rec t)), C ++ [q.2.1]))
                (· = (s, (tws.map fun t ↦ (t, rec t), Cf))) = 0 := by
            intro ans rec ce u
            refine hzero ans rec ce (k u) _ _ fun w hext hw ↦ ?_
            obtain ⟨s', hs', hsf, -⟩ := hext
            have hmem : (q.2.1, rec q.2.1) ∈ w := by
              rw [hw]
              exact List.mem_map.2 ⟨_, ht, rfl⟩
            change w = (Lt.map fun t ↦ (t, rec t)) ++ s' at hs'
            rw [hs'] at hmem
            rcases List.mem_append.1 hmem with h | h
            · rw [wq_tweakReserved_map_pair] at hc
              obtain ⟨t', ht', he⟩ := List.mem_map.1 h
              have e' : t' = q.2.1 := congrArg Prod.fst he
              exact hc (e' ▸ ht')
            · exact (hsf _ h).2 (by simp)
          rw [hz, hz]
        · change prob ((simulateQ (prePlantO P pk ans₁ rec₁ ce₁)
              (k (some (ce₁ q.1 pk q.2.1 q.2.2)))).run _) _ =
            prob ((simulateQ (prePlantO P pk ans₂ rec₂ ce₂)
              (k (some (ce₂ q.1 pk q.2.1 q.2.2)))).run _) _
          rw [hce _ _ _ ht]
          exact ih _ Lt _

/-! ### Lazy sampling: fresh draws versus planted inputs -/

/-- Averaging a value of `xs` at `t` against a function insensitive to `xs t`. -/
theorem wq_sum_update_reindex [Fintype Tw] [Fintype M'] [DecidableEq M'] [Nonempty M'] (t : Tw)
    (F : M' → (Tw → M') → ℝ≥0∞) (hF : ∀ x xs x', F x (Function.update xs t x') = F x xs) :
    ∑ xs : Tw → M', F (xs t) xs =
      ∑ x : M', (Fintype.card M' : ℝ≥0∞)⁻¹ * ∑ xs : Tw → M', F x xs := by
  classical
  have fib : ∀ x x' : M', ∑ xs : Tw → M', (if xs t = x' then F x xs else 0) =
      ∑ xs : Tw → M', (if xs t = x then F x xs else 0) := by
    intro x x'
    let e : (Tw → M') → (Tw → M') := fun xs ↦ Function.update xs t (Equiv.swap x x' (xs t))
    have he : Function.Involutive e := by
      intro xs
      funext j
      by_cases hj : j = t
      · subst hj
        simp [e]
      · simp [e, hj]
    rw [← Equiv.sum_comp he.toPerm]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    simp only [Function.Involutive.coe_toPerm]
    have h1 : e xs t = Equiv.swap x x' (xs t) := by simp [e]
    have h2 : F x (e xs) = F x xs := hF _ _ _
    have h3 : (Equiv.swap x x' (xs t) = x') ↔ (xs t = x) := by
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    simp only [h1, h2, h3]
  have hsum : ∀ x, ∑ xs : Tw → M', F x xs =
      (Fintype.card M' : ℝ≥0∞) * ∑ xs : Tw → M', (if xs t = x then F x xs else 0) := by
    intro x
    calc ∑ xs : Tw → M', F x xs
        = ∑ xs : Tw → M', ∑ x' : M', (if xs t = x' then F x xs else 0) := by
          refine Finset.sum_congr rfl fun xs _ ↦ ?_
          rw [Finset.sum_ite_eq]
          simp
      _ = ∑ x' : M', ∑ xs : Tw → M', (if xs t = x' then F x xs else 0) := Finset.sum_comm
      _ = ∑ _x' : M', ∑ xs : Tw → M', (if xs t = x then F x xs else 0) :=
          Finset.sum_congr rfl fun x' _ ↦ fib x x'
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc0 : (Fintype.card M' : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc ∑ xs : Tw → M', F (xs t) xs
      = ∑ xs : Tw → M', ∑ x : M', (if xs t = x then F x xs else 0) := by
        refine Finset.sum_congr rfl fun xs _ ↦ ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ x : M', ∑ xs : Tw → M', (if xs t = x then F x xs else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hsum x, ← mul_assoc, ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top _), one_mul]

/-- Common first step in front of averaged continuations. -/
lemma wq_prob_bind_avg {α β Ω : Type} [Fintype Ω] (m : ProbComp α) (f : α → ProbComp β)
    (g : Ω → α → ProbComp β) (E : β → Prop) (w : ℝ≥0∞)
    (h : ∀ a, prob (f a) E = ∑ ω, w * prob (g ω a) E) :
    prob (m >>= f) E = ∑ ω, w * prob (m >>= g ω) E := by
  rw [wq_prob_bind_tsum]
  simp only [h, wq_prob_bind_tsum]
  calc ∑' a, prob m (· = a) * ∑ ω, w * prob (g ω a) E
      = ∑' a, ∑ ω, w * (prob m (· = a) * prob (g ω a) E) := by
        refine tsum_congr fun a ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ ↦ by ring
    _ = ∑ ω, ∑' a, w * (prob m (· = a) * prob (g ω a) E) :=
        Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)
    _ = _ := by simp only [ENNReal.tsum_mul_left]

/-- **Lazy sampling for the SM-PRE selection phase.**  Running against the game oracles (a fresh
uniform message per accepted challenge) is the average over a uniform `xs : Tw → M'` of the
planted run with records `xs` and answers `th (t, emb (xs t))`. -/
theorem pre_run_plant [Fintype Tw] [Fintype M'] [DecidableEq M'] [Nonempty M'] [SampleableType M']
    (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) {S : Type}
    (oa : OracleComp (PreSpecG P) S) (σ : SM_DT_PRE_State Tw M')
    (z : S × SM_DT_PRE_State Tw M') :
    prob ((simulateQ (SM_DT_PRE_oracles P pk) oa).run σ) (· = z) =
      ∑ xs : Tw → M', (Fintype.card (Tw → M') : ℝ≥0∞)⁻¹ *
        prob ((simulateQ (prePlantO P pk (fun t ↦ P.th.eval pk t (P.emb (xs t))) xs
          P.thColl.eval) oa).run σ) (· = z) := by
  classical
  set c : ℝ≥0∞ := (Fintype.card (Tw → M') : ℝ≥0∞)⁻¹ with hc
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, prob_pure]
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
      PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero, one_mul]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    obtain ⟨L, C⟩ := σ
    rcases q with n | t | q
    · rw [preReal_unif]
      simp only [prePlant_unif]
      exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2
    · by_cases hcd : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
      · rw [preReal_chal_rej P pk t L C hcd]
        simp only [prePlant_chal_rej P pk _ _ _ t L C hcd]
        exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2
      · rw [preReal_chal_acc P pk t L C hcd, bind_assoc]
        simp only [prePlant_chal_acc P pk _ _ _ t L C hcd, pure_bind]
        set F : M' → (Tw → M') → ℝ≥0∞ := fun x xs ↦
          prob ((simulateQ (prePlantO P pk (fun t ↦ P.th.eval pk t (P.emb (xs t))) xs
            P.thColl.eval) (k (some (P.th.eval pk t (P.emb x))))).run (L ++ [(t, x)], C)) (· = z)
          with hF
        have hFinv : ∀ x xs x', F x (Function.update xs t x') = F x xs := by
          intro x xs x'
          refine (prePlant_congr_used P pk _ _ _ _ _ _ _ C (fun t' ht' ↦ ?_) z).symm
          have hne : t' ≠ t := fun h ↦ ht' (by simp [h])
          exact ⟨by simp [Function.update_of_ne hne], by simp [Function.update_of_ne hne]⟩
        change prob (($ᵗ M' : ProbComp M') >>= fun x ↦
            (simulateQ (SM_DT_PRE_oracles P pk) (k (some (P.th.eval pk t (P.emb x))))).run
              (L ++ [(t, x)], C)) (· = z) = ∑ xs : Tw → M', c * F (xs t) xs
        rw [wq_prob_bind_tsum, tsum_fintype, ← Finset.mul_sum, wq_sum_update_reindex t F hFinv]
        simp only [prob_uniformSample_eq, ih]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun xs _ ↦ by ring
    · rw [preReal_coll]
      simp only [prePlant_coll]
      by_cases hcd : TweakReserved Prod.fst L q.2.1
      · rw [collectionOracle_run_of_challenge_clash Prod.fst q hcd]
        exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2
      · rw [collectionOracle_run_of_fresh Prod.fst q hcd]
        exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2

/-! ### Records of planted runs -/

/-- Every entry recorded by a planted run is `(t, rec t)`. -/
theorem prePlant_run_rec (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (rec : Tw → M') (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) {S : Type}
    (oa : OracleComp (PreSpecG P) S) (σ : SM_DT_PRE_State Tw M') (hσ : ∀ e ∈ σ.1, e.2 = rec e.1) :
    ∀ z ∈ support ((simulateQ (prePlantO P pk ans rec ce) oa).run σ), ∀ e ∈ z.2.1, e.2 = rec e.1 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hσ
  | query_bind q k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff ..).mp hz
    refine ih p.1 p.2 ?_ z hz
    obtain ⟨L, C⟩ := σ
    rcases q with n | t | q
    · rw [prePlant_unif] at hp
      simp only [support_map, Set.mem_image] at hp
      obtain ⟨u, -, rfl⟩ := hp
      exact hσ
    · by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
      · rw [prePlant_chal_rej P pk ans rec ce t L C hc] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hσ
      · rw [prePlant_chal_acc P pk ans rec ce t L C hc] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hσ e he
        · simp only [List.mem_singleton] at he
          subst he
          rfl
    · rw [prePlant_coll] at hp
      by_cases hc : TweakReserved Prod.fst L q.2.1
      · rw [collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hσ
      · rw [collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) Prod.fst q hc] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact hσ

/-- The final state of a planted run with records `rec`, from its skeleton
`(state, challenge tweaks, collection tweaks)`. -/
def preROf {S : Type} (rec : Tw → M') (k : S × List Tw × List Tw) : S × SM_DT_PRE_State Tw M' :=
  (k.1, (k.2.1.map fun t ↦ (t, rec t), k.2.2))

theorem preROf_injective {S : Type} (rec : Tw → M') :
    Function.Injective (preROf (S := S) rec) := by
  rintro ⟨s, tws, C⟩ ⟨s', tws', C'⟩ h
  simp only [preROf, Prod.mk.injEq, wq_map_pair_inj] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- A sum over the outputs of a planted run is a sum over skeletons. -/
theorem tsum_preROf {S : Type} (rec : Tw → M') (f : S × SM_DT_PRE_State Tw M' → ℝ≥0∞)
    (hf : ∀ r, f r ≠ 0 → ∀ e ∈ r.2.1, e.2 = rec e.1) :
    ∑' r, f r = ∑' k : S × List Tw × List Tw, f (preROf rec k) := by
  refine ((preROf_injective rec).tsum_eq fun r hr ↦ ?_).symm
  refine ⟨(r.1, r.2.1.map Prod.fst, r.2.2), ?_⟩
  obtain ⟨s, L, C⟩ := r
  have h := hf _ hr
  simp only [preROf, List.map_map, Prod.mk.injEq, true_and, and_true]
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun e he ↦ ?_
  simp only [Function.comp_apply, id]
  rw [← h e he]

/-! ### The generic row bound -/

/-- Exchange of a countable sum with two finite sums. -/
lemma wq_tsum_sum_sum_swap {K A B : Type} [Fintype A] [Fintype B] (f : K → A → B → ℝ≥0∞) :
    ∑' k, ∑ a, ∑ b, f k a b = ∑ a, ∑ b, ∑' k, f k a b := by
  rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)

/-- The winning event of SM-PRE for the final challenge history `L` and row `R`. -/
def preWin {Y : Type} (L : List (Tw × M')) (R : Tw × M' → Y) (jm : ℕ × M') : Prop :=
  ∃ tx, L[jm.1]? = some tx ∧ R (tx.1, jm.2) = R tx

/-- The tweak of the `j`-th entry of a tweak list (arbitrary when out of range). -/
noncomputable def wqTweakAt [Nonempty Tw] (tws : List Tw) (j : ℕ) : Tw :=
  tws[j]?.getD (Classical.arbitrary Tw)

variable [Fintype Tw] [Fintype M'] [DecidableEq M'] [Nonempty M'] [SampleableType M']
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [AddCommGroup Y] [Nonempty Tw]

/-- **Generic row bound for SM-PRE with a quantum second phase.**  The attacked hash at the seed
`pk`, on the image of `emb`, is a uniformly random row `R : Tw × M' → Y` (`hth`); the collection
reads, at tweak `t`, only the points `(t, ·)` of the row (`hce`); the selection program `choose`
is fixed; the second-phase machine `invert R s` is described, for every state `s`, by a `q`-query
hybrid model over the row (`hModel`).  Then the average over the row of the game's winning weight
at `pk` is at most `(2q+1)² (1/|Y| + 1/|M'|)`. -/
theorem pre_row_avg_le (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (thR : (Tw × M' → Y) → PkSeed → Tw → M → Y) (hth : ∀ R t m, thR R pk t (P.emb m) = R (t, m))
    (ceR : (Tw × M' → Y) → (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    (hce : ∀ R R' i t x, (∀ m, R (t, m) = R' (t, m)) → ceR R i pk t x = ceR R' i pk t x)
    {S : Type} (choose : OracleComp (PreSpecG P) S)
    {W : Type} [Fintype W] (invert : (Tw × M' → Y) → S → Closed W (ℕ × M'))
    (ρ : Matrix W W ℂ) (q : ℕ)
    (hModel : ∀ s, ∃ Mo : PQ.QROM.HybridModel (Tw × M') Y (ℕ × M') q,
      ∀ R (Ev : ℕ × M' → Prop) [DecidablePred Ev], Mo.prob R Ev = qWeight Ev (invert R s) ρ) :
    ∑ R : Tw × M' → Y, (Fintype.card (Tw × M' → Y) : ℝ≥0∞)⁻¹ *
      qWeight (· = true)
        (liftU ((simulateQ (SM_DT_PRE_oracles (preWithEval P (thR R) (ceR R)) pk) choose).run
            ([], [])) >>= fun r ↦
          invert R r.1 >>= fun jm ↦
            liftU (match r.2.1[jm.1]? with
            | none => pure false
            | some tx => pure (decide (thR R pk tx.1 (P.emb jm.2) = thR R pk tx.1 (P.emb tx.2))))) ρ ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card M' : ℝ≥0∞)⁻¹) := by
  classical
  set u : ℝ≥0∞ := (Fintype.card (Tw × M' → Y) : ℝ≥0∞)⁻¹ with hu
  set cX : ℝ≥0∞ := (Fintype.card (Tw → M') : ℝ≥0∞)⁻¹ with hcX
  set B : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 *
    ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card M' : ℝ≥0∞)⁻¹) with hB
  let run : (Tw × M' → Y) → ProbComp (S × SM_DT_PRE_State Tw M') := fun R ↦
    (simulateQ (SM_DT_PRE_oracles (preWithEval P (thR R) (ceR R)) pk) choose).run ([], [])
  let plant : (Tw × M' → Y) → (Tw → M') → ProbComp (S × SM_DT_PRE_State Tw M') := fun R xs ↦
    (simulateQ (prePlantO P pk (fun t ↦ R (t, xs t)) xs (ceR R)) choose).run ([], [])
  let G : (Tw × M' → Y) → S × SM_DT_PRE_State Tw M' → ℝ≥0∞ := fun R r ↦
    qWeight (preWin r.2.1 R) (invert R r.1) ρ
  -- step 1: decompose each game over the first-phase output
  have hdec : ∀ R : Tw × M' → Y,
      qWeight (· = true)
        (liftU (run R) >>= fun r ↦
          invert R r.1 >>= fun jm ↦
            liftU (match r.2.1[jm.1]? with
            | none => pure false
            | some tx => pure (decide (thR R pk tx.1 (P.emb jm.2) = thR R pk tx.1 (P.emb tx.2))))) ρ =
        ∑' r, prob (run R) (· = r) * G R r := by
    intro R
    rw [wq_qWeight_liftU_bind_tsum]
    refine tsum_congr fun r ↦ ?_
    congr 1
    have hc : (fun jm : ℕ × M' ↦
        (liftU (match r.2.1[jm.1]? with
          | none => pure false
          | some tx => pure (decide (thR R pk tx.1 (P.emb jm.2) = thR R pk tx.1 (P.emb tx.2))))
          : Closed W Bool)) =
        fun jm ↦ pure (decide (preWin r.2.1 R jm)) := by
      funext jm
      cases h : r.2.1[jm.1]? with
      | none => simp [preWin, h]
      | some tx => simp [preWin, h, hth]
    rw [hc, wq_qWeight_bind_pure_decide]
  -- step 2: lazy sampling
  have hplant : ∀ R r, prob (run R) (· = r) = ∑ xs : Tw → M', cX * prob (plant R xs) (· = r) := by
    intro R r
    have h := pre_run_plant (preWithEval P (thR R) (ceR R)) pk choose ([], []) r
    have ha : ∀ xs : Tw → M', (fun t ↦ (preWithEval P (thR R) (ceR R)).th.eval pk t
        ((preWithEval P (thR R) (ceR R)).emb (xs t))) = fun t ↦ R (t, xs t) :=
      fun xs ↦ funext fun t ↦ hth R t (xs t)
    simp only [ha] at h
    exact h
  -- step 3: skeletons
  have hskel : ∀ R xs, ∑' r, prob (plant R xs) (· = r) * G R r =
      ∑' k : S × List Tw × List Tw,
        prob (plant R xs) (· = preROf xs k) * G R (preROf xs k) := by
    intro R xs
    refine tsum_preROf xs (fun r ↦ prob (plant R xs) (· = r) * G R r) fun r hr ↦ ?_
    have h0 : prob (plant R xs) (· = r) ≠ 0 := left_ne_zero_of_mul hr
    have hsupp : r ∈ support (plant R xs) := by
      by_contra hn
      exact h0 (wq_prob_eq_zero_of_forall_ne _ _ fun w hw hwr ↦ hn (hwr ▸ hw))
    exact prePlant_run_rec P pk _ xs (ceR R) choose ([], []) (by simp) r hsupp
  have hskel1 : ∀ R xs, ∑' r, prob (plant R xs) (· = r) =
      ∑' k : S × List Tw × List Tw, prob (plant R xs) (· = preROf xs k) := by
    intro R xs
    refine tsum_preROf xs (fun r ↦ prob (plant R xs) (· = r)) fun r h0 ↦ ?_
    have hsupp : r ∈ support (plant R xs) := by
      by_contra hn
      exact h0 (wq_prob_eq_zero_of_forall_ne _ _ fun w hw hwr ↦ hn (hwr ▸ hw))
    exact prePlant_run_rec P pk _ xs (ceR R) choose ([], []) (by simp) r hsupp
  -- step 4: per skeleton, the planted PRE bound
  have hper : ∀ k : S × List Tw × List Tw,
      ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) *
        (prob (plant R xs) (· = preROf xs k) * G R (preROf xs k)) ≤
      B * ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) * prob (plant R xs) (· = preROf xs k) := by
    intro k
    obtain ⟨Mo, hMo⟩ := hModel k.1
    let m₀ : M' := Classical.arbitrary M'
    let y₀ : Y := Classical.arbitrary Y
    let cc : Tw → Bool := fun t ↦ decide (t ∈ k.2.1)
    let o : (Tw → Option Y) → (Tw × M' → Y) → (Tw → M') → ℝ≥0∞ := fun yv R _ ↦
      prob ((simulateQ (prePlantO P pk (fun t ↦ (yv t).getD y₀) (fun _ ↦ m₀) (ceR R)) choose).run
        ([], [])) (· = preROf (fun _ ↦ m₀) k)
    have hrel : ∀ R xs, prob (plant R xs) (· = preROf xs k) = o (PQ.QROM.tvals cc R xs) R xs := by
      intro R xs
      have h := prePlant_relabel P pk (fun t ↦ R (t, xs t)) (fun t ↦ ((PQ.QROM.tvals cc R xs) t).getD y₀)
        xs (fun _ ↦ m₀) (ceR R) (ceR R) choose k.1 k.2.1 k.2.2
        (fun t ht ↦ by simp [PQ.QROM.tvals, cc, ht]) (fun _ _ _ _ ↦ rfl) [] []
      exact h
    have h1 : ∀ k' : Tw × M', cc k'.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × M' → Y)
        (xs : Tw → M') (v : Y), o yv (Function.update R k' v) xs = o yv R xs := by
      intro k' hk' yv R xs v
      have hk : k'.1 ∈ k.2.1 := by simpa [cc] using hk'
      exact prePlant_relabel P pk _ _ _ _ (ceR (Function.update R k' v)) (ceR R) choose k.1 k.2.1 k.2.2
        (fun _ _ ↦ rfl)
        (fun i t x ht ↦ hce _ _ i t x fun m ↦ Function.update_of_ne
          (fun h ↦ ht (by rw [show t = k'.1 from congrArg Prod.fst h]; exact hk)) _ _) [] []
    have h2 : ∀ t : Tw, cc t = true → ∀ (yv : Tw → Option Y) (R : Tw × M' → Y)
        (xs : Tw → M') (m : M'), o yv R (Function.update xs t m) = o yv R xs :=
      fun _ _ _ _ _ _ ↦ rfl
    let out : ℕ × M' → Tw × M' := fun l ↦ (wqTweakAt k.2.1 l.1, l.2)
    have hG := PQ.QROM.pre_embedded_obs_weighted_le (Function.Embedding.refl (Tw × M'))
      (fun _ ↦ y₀) cc o h1 h2 (fun _ ↦ Mo) (fun _ ↦ out) id
    simp only [wq_patch_refl_eq, id] at hG
    refine le_trans (Finset.sum_le_sum fun R _ ↦ Finset.sum_le_sum fun xs _ ↦ ?_)
      (le_trans hG (le_of_eq ?_))
    · rw [hrel R xs]
      refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
      change qWeight (preWin (k.2.1.map fun t ↦ (t, xs t)) R) (invert R k.1) ρ ≤ _
      rw [← hMo R]
      refine Mo.prob_mono R ?_
      rintro jm ⟨tx, htx, heq⟩
      rw [List.getElem?_map] at htx
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 htx
      have hout : out jm = (t, jm.2) := by simp [out, wqTweakAt, ht]
      rw [hout]
      refine ⟨?_, heq⟩
      simp [cc, List.mem_of_getElem? ht]
    · congr 1
      refine Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun xs _ ↦ ?_
      rw [hrel R xs]
  -- step 5: assemble
  have hsumu : ∑ _R : Tw × M' → Y, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu]
    exact PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero
  have hsumx : ∑ _xs : Tw → M', cX = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcX]
    exact PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero
  have hinner : ∀ R : Tw × M' → Y, ∑' r, prob (run R) (· = r) * G R r =
      ∑ xs : Tw → M', cX * ∑' k : S × List Tw × List Tw,
        prob (plant R xs) (· = preROf xs k) * G R (preROf xs k) := by
    intro R
    simp only [hplant, Finset.sum_mul]
    rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    rw [← hskel R xs, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun r ↦ by ring
  change ∑ R : Tw × M' → Y, u * qWeight (· = true) (liftU (run R) >>= _) ρ ≤ B
  simp only [hdec, hinner]
  have hswap : ∀ g : S × List Tw × List Tw → (Tw × M' → Y) → (Tw → M') → ℝ≥0∞,
      ∑ R : Tw × M' → Y, u * ∑ xs : Tw → M', cX * ∑' k : S × List Tw × List Tw, g k R xs =
        ∑' k : S × List Tw × List Tw, ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) * g k R xs := by
    intro g
    rw [wq_tsum_sum_sum_swap]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun k ↦ by ring
  rw [hswap fun k R xs ↦ prob (plant R xs) (· = preROf xs k) * G R (preROf xs k)]
  calc ∑' k : S × List Tw × List Tw, ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) *
        (prob (plant R xs) (· = preROf xs k) * G R (preROf xs k))
      ≤ ∑' k : S × List Tw × List Tw, B * ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) *
          prob (plant R xs) (· = preROf xs k) :=
          tsum_le_tsum hper
    _ = B * ∑ R : Tw × M' → Y, u * ∑ xs : Tw → M', cX * ∑' k : S × List Tw × List Tw,
          prob (plant R xs) (· = preROf xs k) := by
        rw [ENNReal.tsum_mul_left, hswap fun k R xs ↦ prob (plant R xs) (· = preROf xs k)]
    _ = B * ∑ R : Tw × M' → Y, u * ∑ xs : Tw → M', cX * ∑' r, prob (plant R xs) (· = r) := by
        simp only [hskel1]
    _ ≤ B * ∑ _R : Tw × M' → Y, u * ∑ _xs : Tw → M', cX * 1 := by
        gcongr with R _ xs _
        exact wq_tsum_prob_le_one _
    _ = B := by simp only [mul_one, hsumx, hsumu]

end wpre

/-! ## The experiment at a fixed seed -/

section seed

variable {W : Type} [Fintype W] {ι PkSeed Tweak M M' Y : Type} [DecidableEq Tweak] [DecidableEq Y]
  [SampleableType M']

/-- The winning weight of a quantum SM-PRE adversary once the seed `pk` is drawn. -/
noncomputable def preInner {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (SM_DT_PRE_oracles P pk) adv.choose).run ([], [])) >>= fun r ↦
      adv.invert r.1 pk >>= fun jm ↦
        liftU (match r.2.1[jm.1]? with
        | none => pure false
        | some tx => pure (decide (P.th.eval pk tx.1 (P.emb jm.2) = P.th.eval pk tx.1 (P.emb tx.2)))))
    adv.ρ₀

/-- The quantum SM-PRE advantage is the seed average of `preInner` (any seed distribution). -/
theorem qSM_DT_PRE_Advantage_eq_tsum {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_Adversary W P) :
    qSM_DT_PRE_Advantage adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * preInner adv pk := by
  unfold qSM_DT_PRE_Advantage qSM_DT_PRE_Experiment
  simp only [liftU_bind, liftU_pure, bind_assoc, pure_bind]
  rw [wq_qWeight_liftU_bind_tsum]
  rfl

end seed

end PQ.Interactive

#print axioms PQ.Interactive.prePlant_relabel
#print axioms PQ.Interactive.pre_run_plant
#print axioms PQ.Interactive.pre_row_avg_le
#print axioms PQ.Interactive.qSM_DT_PRE_Advantage_eq_tsum
