import Ideal.Direct.Engine

/-!
# Collisions as a budgeted hazard of the pending-charge supermartingale (step 3 of `DIRECT.md` §8)

The plan's "budgeted form" of the 256-bit collision event `Coll`: a hazard of the same
supermartingale as the 128-bit events, with each fresh sample charged at most `(Q + |Z|)/|V|`
under a cap on the number of cached cells, so that `Q` charged steps cost `Q (Q + |Z|)/|V|`.

* `ex_hz_le_of_step_cap`: `Engine.ex_hz_le_of_step` with a **size** of the state that grows by
  at most one per charged query and a step bound required only below the cap `Q` (the induction
  carries `size s + (remaining charged queries) ≤ Q`).
* `CollZ Z κ`: two cached cells with one value, or a cached value in the fixed set `Z` (`IV`,
  the midstate); `collZ_update`: a fresh sample creates a collision only if it equals a cached
  value or lies in `Z`; `prEvent_fresh_coll_le`: probability at most `(|Z| + size κ)/|V|`.
* `hz_or_le`: the hazard of a disjunction is at most the indicator of one disjunct plus the
  `hz` of the other (to add the collision hazard to any pending-charge hazard).
* **`ex_hz_fresh_coll_le`**: one fresh sample into a collision-free cache, with any other hazard
  `P` and pending charge `Ψ` (bounded by `D + Ψ'` as in `Engine.ex_hz_fresh_le`): the expected
  `hz` of `CollZ ∨ P` is at most `(|Z| + size κ)/|V| + D + Ψ'`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.Direct

set_option linter.unusedSectionVars false

/-! ## The capped supermartingale -/

section Cap

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- **Pending-charge supermartingale with a size cap.** -/
theorem ex_hz_le_of_step_cap (so : QueryImpl spec (StateT σ ProbComp)) (I P : σ → Prop)
    (Ψ : σ → ℝ≥0∞) (p : ι → Prop) [DecidablePred p] (ε : ℝ≥0∞) (size : σ → ℕ) (Q : ℕ)
    (hI : ∀ t s, I s → ∀ z ∈ support ((so t).run s), I z.2)
    (habs : ∀ t s, I s → P s → ∀ z ∈ support ((so t).run s), P z.2)
    (hsize : ∀ t s, I s → ∀ z ∈ support ((so t).run s),
      size z.2 ≤ size s + (if p t then 1 else 0))
    (hstep : ∀ t s, I s → ¬ P s → (p t → size s < Q) →
      ex ((so t).run s) (fun z => hz P Ψ z.2) ≤ Ψ s + (if p t then ε else 0))
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) (hs : I s)
    (hQ : size s + n ≤ Q) :
    ex ((simulateQ so oa).run s) (fun z => hz P Ψ z.2) ≤ hz P Ψ s + n * ε := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, ex_pure]
    exact le_self_add
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [run_simulateQ_query_bind, ex_bind]
    set n' := if p t then n - 1 else n with hn'
    have hrest : ∀ z ∈ support ((so t).run s),
        ex ((simulateQ so (k z.1)).run z.2) (fun z => hz P Ψ z.2) ≤ hz P Ψ z.2 + n' * ε := by
      intro z hz'
      refine ih z.1 n' (hn.2 z.1) z.2 (hI t s hs z hz') ?_
      have h1 := hsize t s hs z hz'
      by_cases hpt : p t
      · have hn0 : 0 < n := hn.1.resolve_left (not_not.2 hpt)
        simp only [hn', hpt, ite_true] at h1 ⊢
        omega
      · simp only [hn', hpt, ite_false] at h1 ⊢
        omega
    have hcount : n' * ε + (if p t then ε else 0) ≤ n * ε := by
      by_cases hpt : p t
      · have hn0 : 0 < n := hn.1.resolve_left (not_not.2 hpt)
        obtain ⟨n'', rfl⟩ : ∃ n'', n = n'' + 1 := ⟨n - 1, by omega⟩
        simp [hn', hpt, add_mul]
      · simp [hn', hpt]
    have hlt : p t → size s < Q := fun hpt => by
      have hn0 : 0 < n := hn.1.resolve_left (not_not.2 hpt)
      omega
    by_cases hPs : P s
    · refine (ex_mono_of_support _ (g := fun _ => 1 + n' * ε)
        fun z hz' => (hrest z hz').trans ?_).trans ?_
      · exact le_of_eq (congrArg (· + _) (hz_of_P (habs t s hs hPs z hz')))
      · rw [ex_const, hz_of_P hPs]
        exact add_le_add le_rfl (le_trans le_self_add hcount)
    · refine (ex_mono_of_support _ hrest).trans ?_
      rw [ex_add, ex_const]
      calc _ ≤ (Ψ s + (if p t then ε else 0)) + n' * ε := by
            gcongr; exact hstep t s hs hPs hlt
        _ ≤ hz P Ψ s + n * ε := by
          rw [hz_of_not_P hPs, add_assoc]; gcongr; rw [add_comm]; exact hcount

end Cap

/-! ## Collisions in a cache -/

section Coll

variable {C V : Type} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- The number of cached cells. -/
def csize (κ : C → Option V) : ℕ := (Finset.univ.filter fun q => (κ q).isSome).card

/-- Two cached cells with one value, or a cached value in `Z`. -/
def CollZ (Z : Finset V) (κ : C → Option V) : Prop :=
  (∃ q q' v, q ≠ q' ∧ κ q = some v ∧ κ q' = some v) ∨ ∃ q v, κ q = some v ∧ v ∈ Z

theorem collZ_update (Z : Finset V) (κ : C → Option V) (hκ : ¬ CollZ Z κ) (q : C)
    (hq : κ q = none) (u : V) (h : CollZ Z (Function.update κ q (some u))) :
    u ∈ Z ∨ ∃ q', κ q' = some u := by
  rcases h with ⟨a, b, v, hab, ha, hb⟩ | ⟨a, v, ha, hv⟩
  · by_cases haq : a = q
    · subst haq
      rw [Function.update_self, Option.some.injEq] at ha
      subst ha
      rw [Function.update_of_ne (Ne.symm hab)] at hb
      exact .inr ⟨b, hb⟩
    · rw [Function.update_of_ne haq] at ha
      by_cases hbq : b = q
      · subst hbq
        rw [Function.update_self, Option.some.injEq] at hb
        subst hb
        exact .inr ⟨a, ha⟩
      · rw [Function.update_of_ne hbq] at hb
        exact absurd (.inl ⟨a, b, v, hab, ha, hb⟩) hκ
  · by_cases haq : a = q
    · subst haq
      rw [Function.update_self, Option.some.injEq] at ha
      subst ha
      exact .inl hv
    · rw [Function.update_of_ne haq] at ha
      exact absurd (.inr ⟨a, v, ha, hv⟩) hκ

theorem csize_update (κ : C → Option V) (q : C) (u : V) :
    csize (Function.update κ q (some u)) ≤ csize κ + 1 := by
  unfold csize
  calc (Finset.univ.filter fun q' => (Function.update κ q (some u) q').isSome).card
      ≤ (insert q (Finset.univ.filter fun q' => (κ q').isSome)).card := by
        refine Finset.card_le_card fun q' hq' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq'
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : q' = q
        · exact .inl h
        · rw [Function.update_of_ne h] at hq'; exact .inr hq'
    _ ≤ _ := Finset.card_insert_le _ _

/-- The cached values. -/
noncomputable def cvals (κ : C → Option V) : Finset V :=
  Finset.univ.filter fun v => ∃ q, κ q = some v

theorem cvals_card_le (κ : C → Option V) : (cvals κ).card ≤ csize κ := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have : cvals κ = ∅ := Finset.eq_empty_of_forall_notMem fun v => (IsEmpty.false v).elim
    rw [this, Finset.card_empty]; exact Nat.zero_le _
  unfold cvals csize
  have : (Finset.univ.filter fun v => ∃ q, κ q = some v) ⊆
      (Finset.univ.filter fun q => (κ q).isSome).image fun q => (κ q).getD
        (Classical.arbitrary V) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨q, hq⟩ := hv
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, by simp [hq], by simp [hq]⟩
  exact (Finset.card_le_card this).trans Finset.card_image_le

variable [SampleableType V]

/-- **A fresh sample collides with probability at most `(|Z| + size)/|V|`.** -/
theorem prEvent_fresh_coll_le (Z : Finset V) (κ : C → Option V) :
    Pr{let u ← ($ᵗ V : ProbComp V)}[u ∈ Z ∨ ∃ q', κ q' = some u] ≤
      ((Z.card + csize κ : ℕ) : ℝ≥0∞) / Fintype.card V := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  refine ENNReal.div_le_div_right ?_ _
  have : (Finset.univ.filter fun u : V => u ∈ Z ∨ ∃ q', κ q' = some u) ⊆ Z ∪ cvals κ := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_union, cvals, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hu
  have h2 := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  have h3 := cvals_card_le κ
  exact_mod_cast h2.trans (by omega)

end Coll

/-! ## Adding the collision hazard -/

theorem hz_or_le {σ : Type} (P₁ P₂ : σ → Prop) (Ψ : σ → ℝ≥0∞) (s : σ) :
    hz (fun s => P₁ s ∨ P₂ s) Ψ s ≤ propInd (P₁ s) + hz P₂ Ψ s := by
  by_cases h1 : P₁ s
  · rw [hz_of_P (.inl h1), propInd_eq_one_iff.2 h1]; exact le_self_add
  · rw [propInd_eq_zero_iff.2 h1, zero_add]
    by_cases h2 : P₂ s
    · rw [hz_of_P (.inr h2), hz_of_P h2]
    · rw [hz_of_not_P (fun h => h.elim h1 h2), hz_of_not_P h2]

/-- **One fresh sample, collision hazard added.** -/
theorem ex_hz_fresh_coll_le {C V σ : Type} [Fintype C] [DecidableEq C] [Fintype V]
    [DecidableEq V] [SampleableType V] (Z : Finset V) (κ : C → Option V) (hκ : ¬ CollZ Z κ)
    (q : C) (hq : κ q = none) (upd : V → σ) (cache : σ → C → Option V)
    (hcache : ∀ u, cache (upd u) = Function.update κ q (some u))
    (P : σ → Prop) (Ψ : σ → ℝ≥0∞) (F : V → Prop) (D Ψ' : ℝ≥0∞)
    (hF : ∀ u, P (upd u) → F u) (hD : Pr{let u ← ($ᵗ V : ProbComp V)}[F u] ≤ D)
    (hΨ : ∀ u, Ψ (upd u) ≤ Ψ') :
    ex ($ᵗ V : ProbComp V) (fun u => hz (fun s => CollZ Z (cache s) ∨ P s) Ψ (upd u)) ≤
      ((Z.card + csize κ : ℕ) : ℝ≥0∞) / Fintype.card V + (D + Ψ') := by
  refine (ex_mono _ fun u => hz_or_le _ _ Ψ (upd u)).trans ?_
  rw [ex_add, ← prEvent_eq_ex]
  refine add_le_add ((prEvent_mono _ _ _ fun u hu => ?_).trans (prEvent_fresh_coll_le Z κ))
    (ex_hz_fresh_le _ upd P Ψ F D Ψ' hF hD hΨ)
  rw [hcache] at hu
  exact collZ_update Z κ hκ q hq u hu

end Ideal.Direct

#print axioms Ideal.Direct.ex_hz_le_of_step_cap
#print axioms Ideal.Direct.collZ_update
#print axioms Ideal.Direct.prEvent_fresh_coll_le
#print axioms Ideal.Direct.ex_hz_fresh_coll_le
