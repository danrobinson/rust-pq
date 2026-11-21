import PQ.Interactive.QromBridgeUnif
import PQ.QROM.SprGiven

/-!
# The class-TCR bridge, game side: generic part

Generic (no SLH-DSA) facts about the SM-DT-TCR game of VCVio with a quantum second phase.

* `qWeight_liftU_bind_tsum`: classical sampling in front of a closed machine, for an arbitrary
  (possibly infinite) output type: `qWeight p (liftU oa >>= f) ρ = ∑' x, Pr[oa = x] * qWeight p (f x) ρ`
  (the `Fintype` form is `qWeight_liftU_bind_sum`); `tsum_prob_eq_le_one`.
* The selection phase (`TcrExt`, `tcr_run_ext`, `tcr_run_nodup`): every reachable final
  challenge history extends the initial one by entries with pairwise distinct tweaks, fresh for
  both initial histories; in particular reachable histories have distinct tweaks.
* `tcr_run_prob_congr`: the probability that the selection phase ends in a state whose
  challenge history contains the target `(t₀, m₀)` does not change when the attacked hash is
  changed at the non-target points `(t₀, m)`, `m ≠ m₀`, and the collection at tweak `t₀`
  (collection queries at a reserved tweak are rejected, and a challenge tweak already spent on
  the collection is rejected).  This is the observation-invariance hypothesis `hobs` of
  `PQ.QROM.spr_embedded_obs_weighted_le`.
* **`tcr_row_avg_le`**: if the attacked hash at the seed `pk` is a uniformly random row
  `R : Tw × M → Y`, the collection at tweak `t` reads only `R (t, ·)`, and the second phase is
  described for every first-phase state by a `q`-query hybrid model over the row, then the
  row-average of the game's winning weight at `pk` is at most `(2q+1)²/|Y|`.  No uniformity of the
  seed and no first-phase quantum queries are involved.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}

/-- Congruence of the probability of an event under a common first draw. -/
lemma prob_bind_congr_tcr (mx : ProbComp α) (f g : α → ProbComp β) (E : β → Prop)
    (h : ∀ x, prob (f x) E = prob (g x) E) : prob (mx >>= f) E = prob (mx >>= g) E := by
  unfold prob at h ⊢
  let _ : MeasurableSpace α := ⊤
  have : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  simp only [h]

/-- The output masses of a probabilistic computation sum to at most one. -/
lemma tsum_prob_eq_le_one (oa : ProbComp γ) : ∑' x, prob oa (· = x) ≤ 1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    classical
    simp only [prob_pure, @eq_comm _ a]
    rw [tsum_ite_eq]
  | query_bind n k ih =>
    simp only [prob_unif_query_bind]
    rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    calc ((n : ℝ≥0∞) + 1)⁻¹ * ∑ i, ∑' x, prob (k i) (· = x)
        ≤ ((n : ℝ≥0∞) + 1)⁻¹ * ∑ _i : Fin (n + 1), (1 : ℝ≥0∞) := by
          gcongr with i
          exact ih i
      _ = 1 := unif_avg_const n 1

/-- **Classical sampling in front of a closed machine**, any output type. -/
lemma qWeight_liftU_bind_tsum (p : α → Prop) [DecidablePred p] (oa : ProbComp γ)
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


section smtcr

open TweakableHash

variable {ι PkSeed Tw M Y : Type} [DecidableEq Tw]

/-- `P` with the evaluations of the attacked hash and of the collection replaced (same message
types, same cap). -/
abbrev tcrWithEval (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) (th : PkSeed → Tw → M → Y)
    (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) : SM_DT_TCR_Problem ι PkSeed Tw M Y where
  th := ⟨P.th.seedGen, th⟩
  thColl := ⟨P.thColl.Msg, ce⟩
  numTargets := P.numTargets

/-- Interface of the selection phase. -/
abbrev TcrSpec (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) :=
  unifSpec + (SM_DT_TCR_challengeSpec Tw M Y + collectionSpec P.thColl)

/-- `τ` extends `σ`: the challenge history grows by entries with distinct tweaks, fresh for
both histories of `σ`; the collection list grows. -/
def TcrExt (σ τ : SM_DT_TCR_State Tw M) : Prop :=
  ∃ s, τ.1 = σ.1 ++ s ∧ (s.map Prod.fst).Nodup ∧
    (∀ e ∈ s, e.1 ∉ σ.1.map Prod.fst ∧ e.1 ∉ σ.2) ∧ σ.2 ⊆ τ.2

/-- `TcrExt` is reflexive. -/
theorem tcrExt_refl (σ : SM_DT_TCR_State Tw M) : TcrExt σ σ :=
  ⟨[], by simp, by simp, by simp, fun _ h ↦ h⟩

/-- `TcrExt` is transitive. -/
theorem tcrExt_trans {σ τ υ : SM_DT_TCR_State Tw M} (h₁ : TcrExt σ τ) (h₂ : TcrExt τ υ) :
    TcrExt σ υ := by
  obtain ⟨s, hs, hsn, hsf, hsc⟩ := h₁
  obtain ⟨s', hs', hsn', hsf', hsc'⟩ := h₂
  refine ⟨s ++ s', by rw [hs', hs, List.append_assoc], ?_, ?_, fun x hx ↦ hsc' (hsc hx)⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hsn, hsn', ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
    refine (hsf' e' he').1 ?_
    rw [hs, List.map_append]
    exact List.mem_append_right _ ha
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hsf e he
    · refine ⟨fun hm ↦ (hsf' e he).1 ?_, fun hm ↦ (hsf' e he).2 (hsc hm)⟩
      rw [hs, List.map_append]
      exact List.mem_append_left _ hm

/-- One oracle step of the SM-TCR game extends the state. -/
theorem tcr_step_ext (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) (pk : PkSeed)
    (q : (TcrSpec P).Domain) (σ : SM_DT_TCR_State Tw M) :
    ∀ p ∈ support ((SM_DT_TCR_oracles P pk q).run σ), TcrExt σ p.2 := by
  obtain ⟨L, C⟩ := σ
  rcases q with n | ⟨t, m⟩ | q
  · intro p hp
    have h : (SM_DT_TCR_oracles P pk (.inl n)).run (L, C) =
        (fun u => (u, (L, C))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
      simp [SM_DT_TCR_oracles]
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact tcrExt_refl _
  · intro p hp
    have horc : SM_DT_TCR_oracles P pk (.inr (.inl (t, m))) =
        SM_DT_TCR_challengeOracle P pk (t, m) := rfl
    rw [horc] at hp
    by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
    · have : (SM_DT_TCR_challengeOracle P pk (t, m)).run (L, C) = pure (none, (L, C)) := by
        simp [SM_DT_TCR_challengeOracle, hc]
      rw [this] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact tcrExt_refl _
    · have : (SM_DT_TCR_challengeOracle P pk (t, m)).run (L, C) =
          pure (some (P.th.eval pk t m), (L ++ [(t, m)], C)) := by
        simp [SM_DT_TCR_challengeOracle, hc]
      rw [this] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp only [not_or, not_le, not_not] at hc
      obtain ⟨-, hres, hcoll⟩ := hc
      refine ⟨[(t, m)], rfl, by simp, ?_, fun _ h ↦ h⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      refine ⟨fun hm ↦ hres ?_, hcoll⟩
      obtain ⟨e', he', h'⟩ := List.mem_map.1 hm
      exact ⟨e', he', h'⟩
  · intro p hp
    have horc : SM_DT_TCR_oracles P pk (.inr (.inr q)) =
        collectionOracle (Q := Tw × M) Prod.fst P.thColl pk q := rfl
    rw [horc] at hp
    by_cases hc : TweakReserved Prod.fst L q.2.1
    · rw [collectionOracle_run_of_challenge_clash Prod.fst q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact tcrExt_refl _
    · rw [collectionOracle_run_of_fresh Prod.fst q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨[], by simp, by simp, by simp, fun x hx ↦ List.mem_append_left _ hx⟩

/-- A run of the selection phase extends the state. -/
theorem tcr_run_ext (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) (pk : PkSeed) {S : Type}
    (oa : OracleComp (TcrSpec P) S) (σ : SM_DT_TCR_State Tw M) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles P pk) oa).run σ), TcrExt σ z.2 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact tcrExt_refl _
  | query_bind q k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff ..).mp hz
    exact tcrExt_trans (tcr_step_ext P pk q σ p hp) (ih p.1 p.2 z hz)

/-- Reachable challenge histories have distinct tweaks. -/
theorem tcr_run_nodup (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) (pk : PkSeed) {S : Type}
    (oa : OracleComp (TcrSpec P) S) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles P pk) oa).run ([], [])),
      (z.2.1.map Prod.fst).Nodup := by
  intro z hz
  obtain ⟨s, hs, hsn, -, -⟩ := tcr_run_ext P pk oa ([], []) z hz
  rw [hs]
  simpa using hsn

/-- An output outside the support has probability zero. -/
lemma prob_eq_zero_of_forall_ne {S : Type} (mx : ProbComp S) (z : S)
    (h : ∀ w ∈ support mx, w ≠ z) : PQ.Interactive.prob mx (· = z) = 0 :=
  prEvent_eq_zero_of_not_mem_support mx fun hz ↦ h z hz rfl

/-- **Row modification at a non-target point of a target tweak.**  The probability that the
selection phase ends in a state `z` whose challenge history contains `(t₀, m₀)` is unchanged
when the hash is changed at the points `(t₀, m)`, `m ≠ m₀`, and the collection at tweak `t₀`. -/
theorem tcr_run_prob_congr (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) (pk : PkSeed)
    (th₁ th₂ : PkSeed → Tw → M → Y) (ce₁ ce₂ : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    (t₀ : Tw) (m₀ : M) (hth : ∀ t m, (t = t₀ → m = m₀) → th₁ pk t m = th₂ pk t m)
    (hce : ∀ i t x, t ≠ t₀ → ce₁ i pk t x = ce₂ i pk t x) {S : Type}
    (oa : OracleComp (TcrSpec P) S) (σ : SM_DT_TCR_State Tw M)
    (z : S × SM_DT_TCR_State Tw M) (hz : (t₀, m₀) ∈ z.2.1) :
    PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th₁ ce₁) pk) oa).run σ) (· = z) =
      PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th₂ ce₂) pk) oa).run σ) (· = z) := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    obtain ⟨L, C⟩ := σ
    rcases q with n | ⟨t, m⟩ | q
    · have h : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y),
          (SM_DT_TCR_oracles (tcrWithEval P th ce) pk (.inl n)).run (L, C) =
            (fun u => (u, (L, C))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        intro th ce
        simp [SM_DT_TCR_oracles]
      rw [h th₁ ce₁, h th₂ ce₂]
      exact PQ.Interactive.prob_bind_congr_tcr _ _ _ _ fun p ↦ ih p.1 p.2
    · have horc : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y),
          SM_DT_TCR_oracles (tcrWithEval P th ce) pk (.inr (.inl (t, m))) =
            SM_DT_TCR_challengeOracle (tcrWithEval P th ce) pk (t, m) := fun _ _ ↦ rfl
      rw [horc th₁ ce₁, horc th₂ ce₂]
      by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
      · have h : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y),
            (SM_DT_TCR_challengeOracle (tcrWithEval P th ce) pk (t, m)).run (L, C) = pure (none, (L, C)) := by
          intro th ce
          simp [SM_DT_TCR_challengeOracle, hc]
        rw [h th₁ ce₁, h th₂ ce₂, pure_bind, pure_bind]
        exact ih _ _
      · have h : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y),
            (SM_DT_TCR_challengeOracle (tcrWithEval P th ce) pk (t, m)).run (L, C) =
              pure (some (th pk t m), (L ++ [(t, m)], C)) := by
          intro th ce
          simp [SM_DT_TCR_challengeOracle, hc]
        rw [h th₁ ce₁, h th₂ ce₂, pure_bind, pure_bind]
        by_cases he : t = t₀ → m = m₀
        · change PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th₁ ce₁) pk)
              (k (some (th₁ pk t m)))).run (L ++ [(t, m)], C)) (· = z) =
            PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th₂ ce₂) pk)
              (k (some (th₂ pk t m)))).run (L ++ [(t, m)], C)) (· = z)
          rw [hth t m he]
          exact ih _ _
        · have ⟨ht, hm⟩ : t = t₀ ∧ m ≠ m₀ := ⟨by tauto, by tauto⟩
          subst ht
          simp only [not_or, not_le, not_not] at hc
          obtain ⟨-, hres, -⟩ := hc
          have hzero : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) (u : Option Y),
              PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th ce) pk) (k u)).run (L ++ [(t, m)], C))
                (· = z) = 0 := by
            intro th ce u
            refine prob_eq_zero_of_forall_ne _ _ fun w hw hwz ↦ ?_
            subst hwz
            obtain ⟨s, hs, -, hsf, -⟩ := tcr_run_ext (tcrWithEval P th ce) pk (k u) _ w hw
            rw [hs] at hz
            simp only [List.append_assoc, List.mem_append, List.mem_singleton] at hz
            rcases hz with hz | hz | hz
            · exact hres ⟨_, hz, rfl⟩
            · exact hm (Prod.ext_iff.1 hz).2.symm
            · exact (hsf _ hz).1 (by simp)
          rw [hzero th₁ ce₁, hzero th₂ ce₂]
    · have horc : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y),
          SM_DT_TCR_oracles (tcrWithEval P th ce) pk (.inr (.inr q)) =
            collectionOracle (Q := Tw × M) Prod.fst (tcrWithEval P th ce).thColl pk q := fun _ _ ↦ rfl
      rw [horc th₁ ce₁, horc th₂ ce₂]
      by_cases hc : TweakReserved Prod.fst L q.2.1
      · rw [collectionOracle_run_of_challenge_clash (thColl := (tcrWithEval P th₁ ce₁).thColl) Prod.fst q hc,
          collectionOracle_run_of_challenge_clash (thColl := (tcrWithEval P th₂ ce₂).thColl) Prod.fst q hc, pure_bind, pure_bind]
        exact ih _ _
      · rw [collectionOracle_run_of_fresh (thColl := (tcrWithEval P th₁ ce₁).thColl) Prod.fst q hc,
          collectionOracle_run_of_fresh (thColl := (tcrWithEval P th₂ ce₂).thColl) Prod.fst q hc, pure_bind, pure_bind]
        by_cases he : q.2.1 = t₀
        · have hzero : ∀ (th : PkSeed → Tw → M → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) (u : Option Y),
              PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th ce) pk) (k u)).run (L, C ++ [q.2.1]))
                (· = z) = 0 := by
            intro th ce u
            refine prob_eq_zero_of_forall_ne _ _ fun w hw hwz ↦ ?_
            subst hwz
            obtain ⟨s, hs, -, hsf, -⟩ := tcr_run_ext (tcrWithEval P th ce) pk (k u) _ w hw
            rw [hs] at hz
            rcases List.mem_append.1 hz with hz | hz
            · exact hc ⟨_, hz, he.symm⟩
            · exact (hsf _ hz).2 (by simp [he])
          rw [hzero th₁ ce₁, hzero th₂ ce₂]
        · change PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th₁ ce₁) pk)
              (k (some (ce₁ q.1 pk q.2.1 q.2.2)))).run (L, C ++ [q.2.1])) (· = z) =
            PQ.Interactive.prob ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P th₂ ce₂) pk)
              (k (some (ce₂ q.1 pk q.2.1 q.2.2)))).run (L, C ++ [q.2.1])) (· = z)
          rw [hce _ _ _ he]
          exact ih _ _

end smtcr

/-! ## Event lemmas for closed machines -/

section ev

variable {W : Type} [Fintype W] {α : Type}

/-- The Born weight depends on the event only up to equivalence. -/
lemma qWeight_congr_ev {p p' : α → Prop} [DecidablePred p] [DecidablePred p']
    (h : ∀ a, p a ↔ p' a) (X : Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p X ρ = qWeight p' X ρ := by
  have e : p = p' := funext fun a ↦ propext (h a)
  subst e
  congr

/-- A deterministic Boolean post-processing is an event. -/
lemma qWeight_bind_pure_decide (E : α → Prop) [DecidablePred E] (X : Closed W α)
    (ρ : Matrix W W ℂ) :
    qWeight (· = true) (X >>= fun a ↦ pure (decide (E a))) ρ = qWeight E X ρ := by
  rw [bind_pure_comp, qWeight_map]
  exact qWeight_congr_ev (fun a ↦ by simp) X ρ

end ev

/-! ## The generic row bound -/

section row

open TweakableHash

variable {ι PkSeed Tw M Y : Type} [DecidableEq Tw]

/-- Target assignment of a challenge history: the message of the first entry at tweak `t`. -/
def tcrTargets (L : List (Tw × M)) (t : Tw) : Option M :=
  (L.find? fun e ↦ decide (e.1 = t)).map Prod.snd

/-- A target of the history is an entry. -/
theorem mem_of_tcrTargets {L : List (Tw × M)} {t : Tw} {m : M} (h : tcrTargets L t = some m) :
    (t, m) ∈ L := by
  unfold tcrTargets at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  have h1 := List.mem_of_find?_eq_some he
  have h2 : e.1 = t := by simpa using List.find?_some he
  rw [← h2]
  exact h1

/-- With distinct tweaks, every entry is the target of its tweak. -/
theorem tcrTargets_of_mem {L : List (Tw × M)} (hL : (L.map Prod.fst).Nodup) {e : Tw × M}
    (he : e ∈ L) : tcrTargets L e.1 = some e.2 := by
  induction L with
  | nil => simp at he
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hL
    unfold tcrTargets at ih ⊢
    rw [List.find?_cons]
    by_cases ha : a.1 = e.1
    · simp only [ha, decide_true]
      rcases List.mem_cons.1 he with rfl | he'
      · rfl
      · exact absurd (ha ▸ List.mem_map_of_mem (f := Prod.fst) he') hL.1
    · have he' : e ∈ L := by
        rcases List.mem_cons.1 he with rfl | he'
        · exact absurd rfl ha
        · exact he'
      simp only [ha, decide_false]
      exact ih hL.2 he'

/-- The winning event of the SM-TCR game for the final challenge history `L` and row `R`. -/
def tcrWin {Y : Type} (L : List (Tw × M)) (R : Tw × M → Y) (jm : ℕ × M) : Prop :=
  ∃ tm, L[jm.1]? = some tm ∧ jm.2 ≠ tm.2 ∧ R (tm.1, jm.2) = R tm

/-- The tweak of the `j`-th entry (arbitrary when out of range). -/
noncomputable def tweakAt [Nonempty Tw] (L : List (Tw × M)) (j : ℕ) : Tw :=
  (L[j]?.map Prod.fst).getD (Classical.arbitrary Tw)

variable [Fintype Tw] [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y]
  [Nonempty Tw] [Nonempty Y] [AddCommGroup Y]

/-- Patching along the identity embedding is the row itself. -/
theorem patch_refl_eq (F : Tw × M → Y) (R : Tw × M → Y) :
    PQ.QROM.patch F (Function.Embedding.refl (Tw × M)) R = R := by
  funext z
  exact PQ.QROM.patch_apply F (Function.Embedding.refl (Tw × M)) R z

/-- **Generic row bound for SM-TCR with a quantum second phase.**  The attacked hash at the seed
`pk` is a uniformly random row `R : Tw × M → Y` (`hth`); the collection reads, at tweak `t`,
only the points `(t, ·)` of the row (`hce`); the selection program `choose` is fixed; the
second-phase machine `forge R s` is described, for every state `s`, by a `q`-query hybrid model
over the row (`hModel`).  Then the average over the row of the game's winning weight at `pk` is at
most `(2q+1)²/|Y|`. -/
theorem tcr_row_avg_le (P : SM_DT_TCR_Problem ι PkSeed Tw M Y) (pk : PkSeed)
    (thR : (Tw × M → Y) → PkSeed → Tw → M → Y) (hth : ∀ R t m, thR R pk t m = R (t, m))
    (ceR : (Tw × M → Y) → (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    (hce : ∀ R R' i t x, (∀ m, R (t, m) = R' (t, m)) → ceR R i pk t x = ceR R' i pk t x)
    {S : Type} (choose : OracleComp (TcrSpec P) S)
    {W : Type} [Fintype W] (forge : (Tw × M → Y) → S → Closed W (ℕ × M))
    (ρ : Matrix W W ℂ) (q : ℕ)
    (hModel : ∀ s, ∃ Mo : PQ.QROM.HybridModel (Tw × M) Y (ℕ × M) q,
      ∀ R (Ev : ℕ × M → Prop) [DecidablePred Ev], Mo.prob R Ev = qWeight Ev (forge R s) ρ) :
    ∑ R : Tw × M → Y, (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ *
      qWeight (· = true)
        (liftU ((simulateQ (SM_DT_TCR_oracles (tcrWithEval P (thR R) (ceR R)) pk) choose).run
            ([], [])) >>= fun r ↦
          forge R r.1 >>= fun jm ↦
            match r.2.1[jm.1]? with
            | none => pure false
            | some tm => pure (decide (jm.2 ≠ tm.2 ∧
                thR R pk tm.1 jm.2 = thR R pk tm.1 tm.2))) ρ ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  classical
  set u : ℝ≥0∞ := (Fintype.card (Tw × M → Y) : ℝ≥0∞)⁻¹ with hu
  set ε : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) with hε
  let run : (Tw × M → Y) → ProbComp (S × SM_DT_TCR_State Tw M) := fun R ↦
    (simulateQ (SM_DT_TCR_oracles (tcrWithEval P (thR R) (ceR R)) pk) choose).run ([], [])
  -- step 1: decompose each game over the first-phase output
  have hdec : ∀ R : Tw × M → Y,
      qWeight (· = true)
        (liftU (run R) >>= fun r ↦
          forge R r.1 >>= fun jm ↦
            match r.2.1[jm.1]? with
            | none => pure false
            | some tm => pure (decide (jm.2 ≠ tm.2 ∧
                thR R pk tm.1 jm.2 = thR R pk tm.1 tm.2))) ρ =
        ∑' r, PQ.Interactive.prob (run R) (· = r) * qWeight (tcrWin r.2.1 R) (forge R r.1) ρ := by
    intro R
    rw [qWeight_liftU_bind_tsum]
    refine tsum_congr fun r ↦ ?_
    congr 1
    have hc : (fun jm : ℕ × M ↦
        (match r.2.1[jm.1]? with
          | none => pure false
          | some tm => pure (decide (jm.2 ≠ tm.2 ∧
              thR R pk tm.1 jm.2 = thR R pk tm.1 tm.2)) : Closed W Bool)) =
        fun jm ↦ pure (decide (tcrWin r.2.1 R jm)) := by
      funext jm
      cases h : r.2.1[jm.1]? with
      | none => simp [tcrWin, h]
      | some tm => simp [tcrWin, h, hth]
    rw [hc, qWeight_bind_pure_decide]
  change ∑ R : Tw × M → Y, u * qWeight (· = true) (liftU (run R) >>= _) ρ ≤ ε
  simp only [hdec]
  -- step 2: exchange the row average and the sum over first-phase outputs
  have hswap : ∑ R : Tw × M → Y, u *
      ∑' r, PQ.Interactive.prob (run R) (· = r) * qWeight (tcrWin r.2.1 R) (forge R r.1) ρ =
      ∑' r, ∑ R : Tw × M → Y, u *
        (PQ.Interactive.prob (run R) (· = r) * qWeight (tcrWin r.2.1 R) (forge R r.1) ρ) := by
    simp only [← ENNReal.tsum_mul_left]
    exact (Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)).symm
  rw [hswap]
  -- step 3: for each first-phase output, the weighted SPR bound on the row
  have hper : ∀ r : S × SM_DT_TCR_State Tw M,
      ∑ R : Tw × M → Y, u * (PQ.Interactive.prob (run R) (· = r) *
        qWeight (tcrWin r.2.1 R) (forge R r.1) ρ) ≤
      ε * ∑ R : Tw × M → Y, u * PQ.Interactive.prob (run R) (· = r) := by
    intro r
    obtain ⟨Mo, hMo⟩ := hModel r.1
    let c : Tw → Option M := tcrTargets r.2.1
    let out : ℕ × M → Tw × M := fun l ↦ (tweakAt r.2.1 l.1, l.2)
    have hobs : ∀ (k : Tw × M) (m : M), c k.1 = some m → k.2 ≠ m →
        ∀ (R : Tw × M → Y) (v : Y), PQ.Interactive.prob (run (Function.update R k v)) (· = r) =
          PQ.Interactive.prob (run R) (· = r) := by
      intro k m hc hk R v
      refine tcr_run_prob_congr P pk (thR (Function.update R k v)) (thR R)
        (ceR (Function.update R k v)) (ceR R) k.1 m ?_ ?_ choose ([], []) r (mem_of_tcrTargets hc)
      · intro t m' h
        rw [hth, hth]
        refine Function.update_of_ne (fun hk' ↦ ?_) _ _
        have h1 : t = k.1 := by rw [← hk']
        have h2 : m' = k.2 := by rw [← hk']
        exact hk (h2 ▸ h h1)
      · intro i t x ht
        exact hce _ _ i t x fun m' ↦
          Function.update_of_ne (fun h ↦ ht (by rw [← h])) _ _
    have hspr := PQ.QROM.spr_embedded_obs_weighted_le (Function.Embedding.refl (Tw × M))
      (fun _ ↦ Classical.arbitrary Y) c (fun R ↦ PQ.Interactive.prob (run R) (· = r)) hobs
      (fun _ ↦ Mo) (fun _ ↦ out) id
    simp only [patch_refl_eq, id] at hspr
    refine le_trans (Finset.sum_le_sum fun R _ ↦ ?_) hspr
    refine mul_le_mul' le_rfl ?_
    by_cases h0 : PQ.Interactive.prob (run R) (· = r) = 0
    · simp [h0]
    · have hsupp : r ∈ support (run R) := by
        by_contra hn
        exact h0 (prob_eq_zero_of_forall_ne _ _ fun w hw hwr ↦ hn (hwr ▸ hw))
      have hnd := tcr_run_nodup (tcrWithEval P (thR R) (ceR R)) pk choose r hsupp
      rw [← hMo R (tcrWin r.2.1 R)]
      refine mul_le_mul' le_rfl (Mo.prob_mono R ?_)
      rintro jm ⟨tm, htm, hne, heq⟩
      have hmem : tm ∈ r.2.1 := List.mem_of_getElem? htm
      have hout : out jm = (tm.1, jm.2) := by simp [out, tweakAt, htm]
      refine ⟨tm.2, ?_, ?_, ?_⟩
      · rw [hout]
        exact tcrTargets_of_mem hnd hmem
      · rw [hout]
        exact hne
      · rw [hout]
        exact heq
  -- step 4: sum over first-phase outputs
  have hsumu : ∑ _R : Tw × M → Y, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu]
    exact PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero
  calc ∑' r, ∑ R : Tw × M → Y, u * (PQ.Interactive.prob (run R) (· = r) *
          qWeight (tcrWin r.2.1 R) (forge R r.1) ρ)
      ≤ ∑' r, ε * ∑ R : Tw × M → Y, u * PQ.Interactive.prob (run R) (· = r) :=
        tsum_le_tsum fun r ↦ hper r
    _ = ε * ∑ R : Tw × M → Y, u * ∑' r, PQ.Interactive.prob (run R) (· = r) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [← ENNReal.tsum_mul_left]
        exact Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)
    _ ≤ ε * ∑ _R : Tw × M → Y, u * 1 := by
        gcongr with R
        exact tsum_prob_eq_le_one _
    _ = ε := by simp only [mul_one, hsumu]

end row

/-! ## The experiment at a fixed seed -/

section seed

open TweakableHash

variable {W : Type} [Fintype W] {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak] [DecidableEq M]
  [DecidableEq Y]

/-- The winning weight of a quantum SM-TCR adversary once the seed `pk` is drawn. -/
noncomputable def tcrInner {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (SM_DT_TCR_oracles P pk) adv.choose).run ([], [])) >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2))) adv.ρ₀

/-- The quantum SM-TCR advantage is the seed average of `tcrInner` (any seed distribution). -/
theorem qSM_DT_TCR_Advantage_eq_tsum {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_Adversary W P) :
    qSM_DT_TCR_Advantage adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * tcrInner adv pk := by
  unfold qSM_DT_TCR_Advantage qSM_DT_TCR_Experiment
  rw [qWeight_liftU_bind_tsum]
  rfl

end seed

end PQ.Interactive

#print axioms PQ.Interactive.qWeight_liftU_bind_tsum
#print axioms PQ.Interactive.tsum_prob_eq_le_one
#print axioms PQ.Interactive.tcr_run_ext
#print axioms PQ.Interactive.tcr_run_nodup
#print axioms PQ.Interactive.tcr_run_prob_congr
#print axioms PQ.Interactive.tcr_row_avg_le
#print axioms PQ.Interactive.qSM_DT_TCR_Advantage_eq_tsum
