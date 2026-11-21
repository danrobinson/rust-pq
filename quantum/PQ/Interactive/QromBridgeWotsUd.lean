import PQ.Interactive.QromBridgeWotsPre
import PQ.QROM.WotsPullbackUdTight

/-!
# The WOTS-chain UD bridge, game side: generic part

Generic (no SLH-DSA) facts about VCVio's SM-DT-UD game (`SM_DT_UD_oracles`) with a quantum
second phase.

* `udPlantO P pk ans ce`: the planted oracles (an accepted challenge at `t` answers `ans t`).
* `ud_run_plant` (**lazy sampling**): if every challenge response is `g t z` for a uniform
  `z : Z`, the selection phase has the output distribution of the planted phase with
  `ans t := g t (zs t)`, averaged over a uniform `zs : Tw → Z`.  Real world: `Z = M'`,
  `g t x = th (t, emb x)`; ideal world: `Z = Y`, `g t y = y`.
* `udPlant_congr`: the probability that a planted run ends in a state with challenge tweaks
  `tws` depends on `ans` only on `tws` and on the collection only off `tws`.
* **`ud_row_avg_le`**: with the attacked hash at `pk` a uniformly random row (read through
  `emb`), a collection local in the tweak, uniform hidden inputs and outputs, and, for every
  first-phase state, a second phase with the TIGHT hidden-set bound with `q` queries
  (`PQ.QROM.Tight.TightAvgBound`), the row-averaged real success is at most the row-averaged
  ideal success plus `8 q² / |M'|` (`PQ.QROM.ud_tight_obs_real_le_ideal_add`).
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory TweakableHash
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

section wud

variable {ι PkSeed Tw M M' Y : Type} [DecidableEq Tw]

/-- `P` with the evaluations of the attacked hash and of the collection replaced. -/
abbrev udWithEval (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (th : PkSeed → Tw → M → Y)
    (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) : SM_DT_UD_Problem ι PkSeed Tw M M' Y where
  th := ⟨P.th.seedGen, th⟩
  emb := P.emb
  emb_injective := P.emb_injective
  inputGen := P.inputGen
  outputGen := P.outputGen
  thColl := ⟨P.thColl.Msg, ce⟩
  numTargets := P.numTargets

/-- Interface of the selection phase. -/
abbrev UdSpecG (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) :=
  unifSpec + (SM_DT_UD_challengeSpec Tw Y + collectionSpec P.thColl)

/-- The planted challenge oracle. -/
noncomputable def udPlantChal (N : ℕ) (ans : Tw → Y) :
    QueryImpl (SM_DT_UD_challengeSpec Tw Y) (StateT (SM_DT_UD_State Tw) ProbComp) :=
  fun t => do
    let s ← get
    if N ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then
      return none
    else
      set (s.1 ++ [t], s.2)
      return some (ans t)

/-- The planted oracles of the SM-UD game (collection evaluated by `ce`). -/
noncomputable def udPlantO (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (ans : Tw → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) :
    QueryImpl (UdSpecG P) (StateT (SM_DT_UD_State Tw) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM_DT_UD_State Tw) ProbComp) +
    (udPlantChal P.numTargets ans +
      collectionOracle (Q := Tw) id
        (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y) pk)

/-! ### Step equations -/

section steps

variable (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
  (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)

theorem udPlant_unif (n : ℕ) (σ : SM_DT_UD_State Tw) :
    (udPlantO P pk ans ce (.inl n)).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [udPlantO]

theorem udPlant_chal_rej (t : Tw) (L C : List Tw)
    (hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t) :
    (udPlantO P pk ans ce (.inr (.inl t))).run (L, C) = pure (none, (L, C)) := by
  change (udPlantChal P.numTargets ans t).run (L, C) = _
  simp [udPlantChal, hc]

theorem udPlant_chal_acc (t : Tw) (L C : List Tw)
    (hc : ¬ (P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t)) :
    (udPlantO P pk ans ce (.inr (.inl t))).run (L, C) = pure (some (ans t), (L ++ [t], C)) := by
  change (udPlantChal P.numTargets ans t).run (L, C) = _
  simp [udPlantChal, hc]

theorem udPlant_coll (q : (i : ι) × Tw × P.thColl.Msg i) (σ : SM_DT_UD_State Tw) :
    (udPlantO P pk ans ce (.inr (.inr q))).run σ =
      (collectionOracle (Q := Tw) id
        (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y) pk q).run σ := rfl

variable (world : SM_DT_UD_World)

theorem udReal_unif (n : ℕ) (σ : SM_DT_UD_State Tw) :
    (SM_DT_UD_oracles world P pk (.inl n)).run σ =
      (fun u => (u, σ)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [SM_DT_UD_oracles]

theorem udReal_chal_rej (t : Tw) (L C : List Tw)
    (hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t) :
    (SM_DT_UD_oracles world P pk (.inr (.inl t))).run (L, C) = pure (none, (L, C)) := by
  change (SM_DT_UD_challengeOracle world P pk t).run (L, C) = _
  simp [SM_DT_UD_challengeOracle, hc]

theorem udReal_chal_acc (t : Tw) (L C : List Tw)
    (hc : ¬ (P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t)) :
    (SM_DT_UD_oracles world P pk (.inr (.inl t))).run (L, C) =
      (SM_DT_UD_response world P pk t >>= fun y ↦ pure (some y, (L ++ [t], C))) := by
  change (SM_DT_UD_challengeOracle world P pk t).run (L, C) = _
  simp [SM_DT_UD_challengeOracle, hc]

theorem udReal_coll (q : (i : ι) × Tw × P.thColl.Msg i) (σ : SM_DT_UD_State Tw) :
    (SM_DT_UD_oracles world P pk (.inr (.inr q))).run σ =
      (collectionOracle (Q := Tw) id P.thColl pk q).run σ := rfl

end steps

/-! ### Reachable states and invariance of planted runs -/

/-- `τ` extends `σ` (UD states): the challenge list grows by tweaks fresh for both lists of `σ`;
the collection list grows. -/
def UdExt (σ τ : SM_DT_UD_State Tw) : Prop :=
  ∃ s, τ.1 = σ.1 ++ s ∧ (∀ e ∈ s, e ∉ σ.1 ∧ e ∉ σ.2) ∧ σ.2 ⊆ τ.2

theorem udExt_refl (σ : SM_DT_UD_State Tw) : UdExt σ σ := ⟨[], by simp, by simp, fun _ h ↦ h⟩

theorem udExt_trans {σ τ υ : SM_DT_UD_State Tw} (h₁ : UdExt σ τ) (h₂ : UdExt τ υ) :
    UdExt σ υ := by
  obtain ⟨s, hs, hsf, hsc⟩ := h₁
  obtain ⟨s', hs', hsf', hsc'⟩ := h₂
  refine ⟨s ++ s', by rw [hs', hs, List.append_assoc], ?_, fun x hx ↦ hsc' (hsc hx)⟩
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hsf e he
  · refine ⟨fun hm ↦ (hsf' e he).1 ?_, fun hm ↦ (hsf' e he).2 (hsc hm)⟩
    rw [hs]
    exact List.mem_append_left _ hm

theorem wq_tweakReserved_id (L : List Tw) (t : Tw) : TweakReserved id L t ↔ t ∈ L := by
  simp [TweakReserved]

theorem udPlant_step_ext (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) (q : (UdSpecG P).Domain)
    (σ : SM_DT_UD_State Tw) :
    ∀ p ∈ support ((udPlantO P pk ans ce q).run σ), UdExt σ p.2 := by
  obtain ⟨L, C⟩ := σ
  rcases q with n | t | q
  · intro p hp
    rw [udPlant_unif] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact udExt_refl _
  · intro p hp
    by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t
    · rw [udPlant_chal_rej P pk ans ce t L C hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact udExt_refl _
    · rw [udPlant_chal_acc P pk ans ce t L C hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp only [not_or, not_le, not_not] at hc
      obtain ⟨-, hres, hcoll⟩ := hc
      refine ⟨[t], rfl, ?_, fun _ h ↦ h⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨fun hm ↦ hres ((wq_tweakReserved_id L e).2 hm), hcoll⟩
  · intro p hp
    rw [udPlant_coll] at hp
    by_cases hc : TweakReserved id L q.2.1
    · rw [collectionOracle_run_of_challenge_clash
        (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact udExt_refl _
    · rw [collectionOracle_run_of_fresh
        (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨[], by simp, by simp, fun x hx ↦ List.mem_append_left _ hx⟩

theorem udPlant_run_ext (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (ans : Tw → Y)
    (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) {S : Type}
    (oa : OracleComp (UdSpecG P) S) (σ : SM_DT_UD_State Tw) :
    ∀ z ∈ support ((simulateQ (udPlantO P pk ans ce) oa).run σ), UdExt σ z.2 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact udExt_refl _
  | query_bind q k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff ..).mp hz
    exact udExt_trans (udPlant_step_ext P pk ans ce q σ p hp) (ih p.1 p.2 z hz)

/-- A planted run does not read `ans` at tweaks already in the challenge list. -/
theorem udPlant_congr_used (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (ans ans' : Tw → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    {S : Type} (oa : OracleComp (UdSpecG P) S) (L C : List Tw)
    (h : ∀ t, t ∉ L → ans t = ans' t) (z : S × SM_DT_UD_State Tw) :
    prob ((simulateQ (udPlantO P pk ans ce) oa).run (L, C)) (· = z) =
      prob ((simulateQ (udPlantO P pk ans' ce) oa).run (L, C)) (· = z) := by
  induction oa using OracleComp.inductionOn generalizing L C with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with n | t | q
    · rw [udPlant_unif, udPlant_unif, bind_map_left, bind_map_left]
      exact wq_prob_bind_congr _ _ _ _ _ fun u ↦ ih u L C h
    · by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t
      · rw [udPlant_chal_rej P pk ans ce t L C hc, udPlant_chal_rej P pk ans' ce t L C hc,
          pure_bind, pure_bind]
        exact ih _ L C h
      · rw [udPlant_chal_acc P pk ans ce t L C hc, udPlant_chal_acc P pk ans' ce t L C hc,
          pure_bind, pure_bind]
        have ht : t ∉ L := by
          simp only [not_or, not_le, not_not] at hc
          exact fun hm ↦ hc.2.1 ((wq_tweakReserved_id L t).2 hm)
        rw [h t ht]
        exact ih _ _ C fun t' ht' ↦ h t' fun hm ↦ ht' (List.mem_append_left _ hm)
    · rw [udPlant_coll, udPlant_coll]
      by_cases hc : TweakReserved id L q.2.1
      · rw [collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc,
          pure_bind, pure_bind]
        exact ih _ L C h
      · rw [collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc,
          pure_bind, pure_bind]
        exact ih _ L _ h

/-- **Congruence.**  The probability that a planted run ends in `z` depends on the answers only
at the final challenge tweaks `z.2.1`, and on the collection only off them. -/
theorem udPlant_congr (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (ans₁ ans₂ : Tw → Y) (ce₁ ce₂ : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y) {S : Type}
    (oa : OracleComp (UdSpecG P) S) (z : S × SM_DT_UD_State Tw)
    (hans : ∀ t ∈ z.2.1, ans₁ t = ans₂ t) (hce : ∀ i t x, t ∉ z.2.1 → ce₁ i pk t x = ce₂ i pk t x)
    (σ : SM_DT_UD_State Tw) :
    prob ((simulateQ (udPlantO P pk ans₁ ce₁) oa).run σ) (· = z) =
      prob ((simulateQ (udPlantO P pk ans₂ ce₂) oa).run σ) (· = z) := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hzero : ∀ (ans : Tw → Y) (ce : (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
        (oa' : OracleComp (UdSpecG P) S) (σ' : SM_DT_UD_State Tw),
        (UdExt σ' z.2 → False) →
        prob ((simulateQ (udPlantO P pk ans ce) oa').run σ') (· = z) = 0 := by
      intro ans ce oa' σ' hf
      refine wq_prob_eq_zero_of_forall_ne _ _ fun w hw hwz ↦ ?_
      have := udPlant_run_ext P pk ans ce oa' σ' w hw
      rw [hwz] at this
      exact hf this
    obtain ⟨L, C⟩ := σ
    rcases q with n | t | q
    · rw [udPlant_unif, udPlant_unif, bind_map_left, bind_map_left]
      exact wq_prob_bind_congr _ _ _ _ _ fun u ↦ ih u _
    · by_cases hc : P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t
      · rw [udPlant_chal_rej P pk ans₁ ce₁ t L C hc, udPlant_chal_rej P pk ans₂ ce₂ t L C hc,
          pure_bind, pure_bind]
        exact ih _ _
      · rw [udPlant_chal_acc P pk ans₁ ce₁ t L C hc, udPlant_chal_acc P pk ans₂ ce₂ t L C hc,
          pure_bind, pure_bind]
        by_cases ht : t ∈ z.2.1
        · rw [hans t ht]
          exact ih _ _
        · have hf : UdExt (L ++ [t], C) z.2 → False := by
            rintro ⟨s', hs', -, -⟩
            exact ht (by rw [hs']; simp)
          rw [hzero _ _ _ _ hf, hzero _ _ _ _ hf]
    · rw [udPlant_coll, udPlant_coll]
      by_cases hc : TweakReserved id L q.2.1
      · rw [collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce₁⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc,
          collectionOracle_run_of_challenge_clash
          (thColl := (⟨P.thColl.Msg, ce₂⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc,
          pure_bind, pure_bind]
        exact ih _ _
      · rw [collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce₁⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc,
          collectionOracle_run_of_fresh
          (thColl := (⟨P.thColl.Msg, ce₂⟩ : TweakableHashCollection ι PkSeed Tw Y)) id q hc,
          pure_bind, pure_bind]
        by_cases ht : q.2.1 ∈ z.2.1
        · have hf : UdExt (L, C ++ [q.2.1]) z.2 → False := by
            rintro ⟨s', hs', hsf, -⟩
            change z.2.1 = L ++ s' at hs'
            rw [hs'] at ht
            rcases List.mem_append.1 ht with h | h
            · exact hc ((wq_tweakReserved_id L _).2 h)
            · exact (hsf _ h).2 (by simp)
          rw [hzero _ _ _ _ hf, hzero _ _ _ _ hf]
        · change prob ((simulateQ (udPlantO P pk ans₁ ce₁)
              (k (some (ce₁ q.1 pk q.2.1 q.2.2)))).run _) _ =
            prob ((simulateQ (udPlantO P pk ans₂ ce₂)
              (k (some (ce₂ q.1 pk q.2.1 q.2.2)))).run _) _
          rw [hce _ _ _ ht]
          exact ih _ _

/-! ### Lazy sampling -/

/-- **Lazy sampling for the SM-UD selection phase.**  If every challenge response is `g t z` for a
uniform `z : Z`, the run against the game oracles is the average over a uniform `zs : Tw → Z` of
the planted run with answers `g t (zs t)`. -/
theorem ud_run_plant [Fintype Tw] {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    [SampleableType Z] (world : SM_DT_UD_World) (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y)
    (pk : PkSeed) (g : Tw → Z → Y)
    (hresp : ∀ t, SM_DT_UD_response world P pk t = (($ᵗ Z : ProbComp Z) >>= fun z ↦ pure (g t z)))
    {S : Type} (oa : OracleComp (UdSpecG P) S) (σ : SM_DT_UD_State Tw)
    (z : S × SM_DT_UD_State Tw) :
    prob ((simulateQ (SM_DT_UD_oracles world P pk) oa).run σ) (· = z) =
      ∑ zs : Tw → Z, (Fintype.card (Tw → Z) : ℝ≥0∞)⁻¹ *
        prob ((simulateQ (udPlantO P pk (fun t ↦ g t (zs t)) P.thColl.eval) oa).run σ) (· = z) := by
  classical
  set c : ℝ≥0∞ := (Fintype.card (Tw → Z) : ℝ≥0∞)⁻¹ with hc
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, prob_pure]
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
      PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero, one_mul]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    obtain ⟨L, C⟩ := σ
    rcases q with n | t | q
    · rw [udReal_unif]
      simp only [udPlant_unif]
      exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2
    · by_cases hcd : P.numTargets ≤ L.length ∨ ¬ TweakFresh id L C t
      · rw [udReal_chal_rej P pk world t L C hcd]
        simp only [udPlant_chal_rej P pk _ _ t L C hcd]
        exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2
      · rw [udReal_chal_acc P pk world t L C hcd, hresp, bind_assoc]
        simp only [udPlant_chal_acc P pk _ _ t L C hcd, pure_bind, bind_assoc]
        set F : Z → (Tw → Z) → ℝ≥0∞ := fun x zs ↦
          prob ((simulateQ (udPlantO P pk (fun t ↦ g t (zs t)) P.thColl.eval)
            (k (some (g t x)))).run (L ++ [t], C)) (· = z) with hF
        have hFinv : ∀ x zs x', F x (Function.update zs t x') = F x zs := by
          intro x zs x'
          refine (udPlant_congr_used P pk _ _ _ _ _ _ (fun t' ht' ↦ ?_) z).symm
          have hne : t' ≠ t := fun h ↦ ht' (by simp [h])
          simp [Function.update_of_ne hne]
        change prob (($ᵗ Z : ProbComp Z) >>= fun x ↦
            (simulateQ (SM_DT_UD_oracles world P pk) (k (some (g t x)))).run
              (L ++ [t], C)) (· = z) = ∑ zs : Tw → Z, c * F (zs t) zs
        rw [wq_prob_bind_tsum, tsum_fintype, ← Finset.mul_sum, wq_sum_update_reindex t F hFinv]
        simp only [prob_uniformSample_eq, ih]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun xs _ ↦ by ring
    · rw [udReal_coll]
      simp only [udPlant_coll]
      by_cases hcd : TweakReserved id L q.2.1
      · rw [collectionOracle_run_of_challenge_clash id q hcd]
        exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2
      · rw [collectionOracle_run_of_fresh id q hcd]
        exact wq_prob_bind_avg _ _ _ _ _ fun p ↦ ih p.1 p.2

/-! ### The generic row bound -/

variable [Fintype Tw] [Fintype M'] [DecidableEq M'] [Nonempty M'] [SampleableType M']
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [AddCommGroup Y] [SampleableType Y]

/-- **Generic row bound for SM-UD with a quantum second phase (real ≤ ideal + `8 q²/|M'|`).** -/
theorem ud_row_avg_le (P : SM_DT_UD_Problem ι PkSeed Tw M M' Y) (pk : PkSeed)
    (thR : (Tw × M' → Y) → PkSeed → Tw → M → Y) (hth : ∀ R t m, thR R pk t (P.emb m) = R (t, m))
    (ceR : (Tw × M' → Y) → (i : ι) → PkSeed → Tw → P.thColl.Msg i → Y)
    (hce : ∀ R R' i t x, (∀ m, R (t, m) = R' (t, m)) → ceR R i pk t x = ceR R' i pk t x)
    (hin : P.inputGen = $ᵗ M') (hout : P.outputGen = $ᵗ Y)
    {S : Type} (pick : OracleComp (UdSpecG P) S)
    {W : Type} [Fintype W] (dist : (Tw × M' → Y) → S → Closed W Bool)
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (q : ℕ)
    (hT : ∀ s, ∃ f : (Tw × M' → Y) → ℝ≥0∞, PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q ∧
      ∀ R, f R = qWeight (· = true) (dist R s) ρ) :
    ∑ R : Tw × M' → Y, (Fintype.card (Tw × M' → Y) : ℝ≥0∞)⁻¹ *
      qWeight (· = true)
        (liftU ((simulateQ (SM_DT_UD_oracles .real (udWithEval P (thR R) (ceR R)) pk) pick).run
            ([], [])) >>= fun r ↦ dist R r.1) ρ ≤
      ∑ R : Tw × M' → Y, (Fintype.card (Tw × M' → Y) : ℝ≥0∞)⁻¹ *
        qWeight (· = true)
          (liftU ((simulateQ (SM_DT_UD_oracles .ideal (udWithEval P (thR R) (ceR R)) pk) pick).run
              ([], [])) >>= fun r ↦ dist R r.1) ρ +
        ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card M') := by
  classical
  set u : ℝ≥0∞ := (Fintype.card (Tw × M' → Y) : ℝ≥0∞)⁻¹ with hu
  set cX : ℝ≥0∞ := (Fintype.card (Tw → M') : ℝ≥0∞)⁻¹ with hcX
  set cY : ℝ≥0∞ := (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ with hcY
  set δ : ℝ≥0∞ := ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card M') with hδ
  let run : SM_DT_UD_World → (Tw × M' → Y) → ProbComp (S × SM_DT_UD_State Tw) := fun w R ↦
    (simulateQ (SM_DT_UD_oracles w (udWithEval P (thR R) (ceR R)) pk) pick).run ([], [])
  let G : (Tw × M' → Y) → S → ℝ≥0∞ := fun R s ↦ qWeight (· = true) (dist R s) ρ
  let y₀ : Y := Classical.arbitrary Y
  let cc : S × SM_DT_UD_State Tw → Tw → Bool := fun r t ↦ decide (t ∈ r.2.1)
  let o : S × SM_DT_UD_State Tw → (Tw → Option Y) → (Tw × M' → Y) → ℝ≥0∞ := fun r yv R ↦
    prob ((simulateQ (udPlantO P pk (fun t ↦ (yv t).getD y₀) (ceR R)) pick).run ([], [])) (· = r)
  have hdec : ∀ w R, qWeight (· = true) (liftU (run w R) >>= fun r ↦ dist R r.1) ρ =
      ∑' r, prob (run w R) (· = r) * G R r.1 := fun w R ↦ wq_qWeight_liftU_bind_tsum _ _ _ _
  have hreal : ∀ R r, prob (run .real R) (· = r) =
      ∑ xs : Tw → M', cX * o r (PQ.QROM.tvals (cc r) R xs) R := by
    intro R r
    have h := ud_run_plant (Z := M') .real (udWithEval P (thR R) (ceR R)) pk (fun t x ↦ R (t, x))
      (fun t ↦ by
        change (P.inputGen >>= fun x ↦ pure (thR R pk t (P.emb x))) = _
        rw [hin]
        simp only [hth]) pick ([], []) r
    refine h.trans (Finset.sum_congr rfl fun xs _ ↦ ?_)
    congr 1
    exact udPlant_congr P pk _ _ _ _ pick r
      (fun t ht ↦ by simp [PQ.QROM.tvals, cc, ht]) (fun _ _ _ _ ↦ rfl) ([], [])
  have hideal : ∀ R r, prob (run .ideal R) (· = r) =
      ∑ ys : Tw → Y, cY * o r (PQ.QROM.yvals (cc r) ys) R := by
    intro R r
    have h := ud_run_plant (Z := Y) .ideal (udWithEval P (thR R) (ceR R)) pk (fun _ y ↦ y)
      (fun t ↦ by
        change P.outputGen = _
        rw [hout, bind_pure]) pick ([], []) r
    refine h.trans (Finset.sum_congr rfl fun ys _ ↦ ?_)
    congr 1
    exact udPlant_congr P pk _ _ _ _ pick r
      (fun t ht ↦ by simp [PQ.QROM.yvals, cc, ht]) (fun _ _ _ _ ↦ rfl) ([], [])
  -- exchange of sums
  have hswX : ∀ b : S × SM_DT_UD_State Tw → (Tw × M' → Y) → ℝ≥0∞,
      ∑ R : Tw × M' → Y, u * ∑' r, prob (run .real R) (· = r) * b r R =
        ∑' r, ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) *
          (o r (PQ.QROM.tvals (cc r) R xs) R * b r R) := by
    intro b
    rw [wq_tsum_sum_sum_swap]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    simp only [hreal, Finset.sum_mul]
    rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable), Finset.mul_sum]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun r ↦ by ring
  have hswY : ∀ b : S × SM_DT_UD_State Tw → (Tw × M' → Y) → ℝ≥0∞,
      ∑ R : Tw × M' → Y, u * ∑' r, prob (run .ideal R) (· = r) * b r R =
        ∑' r, ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) *
          (o r (PQ.QROM.yvals (cc r) ys) R * b r R) := by
    intro b
    rw [wq_tsum_sum_sum_swap]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    simp only [hideal, Finset.sum_mul]
    rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ys _ ↦ ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun r ↦ by ring
  -- per first-phase output: the tight bound
  have hper : ∀ r : S × SM_DT_UD_State Tw,
      ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) * (o r (PQ.QROM.tvals (cc r) R xs) R * G R r.1) ≤
        ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) * (o r (PQ.QROM.yvals (cc r) ys) R * G R r.1) +
          δ * ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) * (o r (PQ.QROM.yvals (cc r) ys) R * 1) := by
    intro r
    obtain ⟨f, hf, hfe⟩ := hT r.1
    have hG : ∀ R, G R r.1 = f R := fun R ↦ (hfe R).symm
    simp only [hG, mul_one]
    have h1 : ∀ k : Tw × M', cc r k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × M' → Y) (v : Y),
        o r yv (Function.update R k v) = o r yv R := by
      intro k hk yv R v
      have hk' : k.1 ∈ r.2.1 := by simpa [cc] using hk
      exact udPlant_congr P pk _ _ (ceR (Function.update R k v)) (ceR R) pick r (fun _ _ ↦ rfl)
        (fun i t x ht ↦ hce _ _ i t x fun m ↦ Function.update_of_ne
          (fun h ↦ ht (by rw [show t = k.1 from congrArg Prod.fst h]; exact hk')) _ _) ([], [])
    have hofin : ∀ yv R, o r yv R ≠ ⊤ := fun yv R ↦
      ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
    have hf1 : ∀ H, f H ≤ 1 := fun H ↦ by
      rw [hfe H]
      exact qWeight_le_one _ _ hρ hρ1
    exact PQ.QROM.ud_tight_obs_real_le_ideal_add (cc r) (o r) h1 hofin f hf1 q hf
  -- assemble
  change ∑ R : Tw × M' → Y, u * qWeight (· = true) (liftU (run .real R) >>= _) ρ ≤
    ∑ R : Tw × M' → Y, u * qWeight (· = true) (liftU (run .ideal R) >>= _) ρ + δ
  simp only [hdec]
  rw [hswX fun r R ↦ G R r.1, hswY fun r R ↦ G R r.1]
  have hsumu : ∑ _R : Tw × M' → Y, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu]
    exact PQ.QROM.natCast_mul_inv_cancel Fintype.card_ne_zero
  have hmass : ∑' r, ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) *
      (o r (PQ.QROM.yvals (cc r) ys) R * 1) ≤ 1 := by
    rw [← hswY fun _ _ ↦ 1]
    calc ∑ R : Tw × M' → Y, u * ∑' r, prob (run .ideal R) (· = r) * 1
        ≤ ∑ _R : Tw × M' → Y, u * 1 := by
          gcongr with R _
          simp only [mul_one]
          exact wq_tsum_prob_le_one _
      _ = 1 := by simp only [mul_one, hsumu]
  calc ∑' r, ∑ R : Tw × M' → Y, ∑ xs : Tw → M', (u * cX) *
        (o r (PQ.QROM.tvals (cc r) R xs) R * G R r.1)
      ≤ ∑' r, (∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) *
          (o r (PQ.QROM.yvals (cc r) ys) R * G R r.1) +
          δ * ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) *
            (o r (PQ.QROM.yvals (cc r) ys) R * 1)) := tsum_le_tsum hper
    _ = ∑' r, ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) *
          (o r (PQ.QROM.yvals (cc r) ys) R * G R r.1) +
        δ * ∑' r, ∑ R : Tw × M' → Y, ∑ ys : Tw → Y, (u * cY) *
            (o r (PQ.QROM.yvals (cc r) ys) R * 1) := by
        rw [tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        gcongr
        calc δ * _ ≤ δ * 1 := by gcongr
          _ = δ := mul_one δ

end wud

/-! ## The experiment at a fixed seed -/

section seed

variable {W : Type} [Fintype W] {ι PkSeed Tweak M M' Y : Type} [DecidableEq Tweak]

/-- The success weight of a quantum SM-UD adversary in `world` once the seed `pk` is drawn. -/
noncomputable def udInner (world : SM_DT_UD_World) {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (SM_DT_UD_oracles world P pk) adv.pick).run ([], [])) >>= fun r ↦
      adv.distinguish r.1 pk) adv.ρ₀

theorem qSM_DT_UD_RealSuccess_eq_tsum {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_RealSuccess adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * udInner .real adv pk := by
  unfold qSM_DT_UD_RealSuccess qSM_DT_UD_Experiment
  simp only [liftU_bind, liftU_pure, bind_assoc, pure_bind, bind_pure]
  rw [wq_qWeight_liftU_bind_tsum]
  rfl

theorem qSM_DT_UD_IdealSuccess_eq_tsum {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_IdealSuccess adv =
      ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * udInner .ideal adv pk := by
  unfold qSM_DT_UD_IdealSuccess qSM_DT_UD_Experiment
  simp only [liftU_bind, liftU_pure, bind_assoc, pure_bind, bind_pure]
  rw [wq_qWeight_liftU_bind_tsum]
  rfl

end seed

end PQ.Interactive

#print axioms PQ.Interactive.udPlant_congr
#print axioms PQ.Interactive.ud_run_plant
#print axioms PQ.Interactive.ud_row_avg_le
#print axioms PQ.Interactive.qSM_DT_UD_RealSuccess_eq_tsum
#print axioms PQ.Interactive.qSM_DT_UD_IdealSuccess_eq_tsum
