import PQ.QROM.UdGiven
import PQ.QROM.PurifyInstances

/-!
# Tight undetectability on a random row, with observations and weights

The setting of `PQ.QROM.ud_embedded_real_le_ideal_add` (`PQ/QROM/UdGiven.lean`) with the
identity embedding and a fixed algorithm, but with the TIGHT hidden-set bound
(`PQ.QROM.Tight.TightAvgBound`, `PQ/QROM/PurifyInstances.lean`) in place of a `HybridModel`:

* real world: `R : Tw × Msg → Y` and `xs : Tw → Msg` uniform, target values `tvals c R xs`;
* ideal world: `R` and `ys : Tw → Y` uniform, target values `yvals c ys`;
* the weight `o targets R` ignores the requested rows of `R` (`h1`); the algorithm is a
  functional `f` of the oracle `R` with the tight bound with `q` queries.

`ud_tight_obs_real_le_ideal_add`: the weighted probability of the real world is at most that of
the ideal world plus `8 q² / |Msg|` times the average weight.
-/

open ENNReal Finset

set_option linter.unusedSectionVars false

namespace PQ.QROM

section

variable {Tw Msg Y : Type} [Fintype Tw] [DecidableEq Tw] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Msg] [Nonempty Y]

/-- `ENNReal` sum of finite terms as `ofReal` of the real sum. -/
theorem wq_sum_eq_ofReal {Ω : Type} [Fintype Ω] (a : Ω → ℝ≥0∞) (ha : ∀ ω, a ω ≠ ⊤) :
    ∑ ω, a ω = ENNReal.ofReal (∑ ω, (a ω).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ ENNReal.toReal_nonneg]
  exact Finset.sum_congr rfl fun ω _ ↦ (ENNReal.ofReal_toReal (ha ω)).symm

/-- **Tight UD on a random row, with observations and weights (real ≤ ideal + error).** -/
theorem ud_tight_obs_real_le_ideal_add (c : Tw → Bool)
    (o : (Tw → Option Y) → (Tw × Msg → Y) → ℝ≥0∞)
    (h1 : ∀ k : Tw × Msg, c k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y) (v : Y),
      o yv (Function.update R k v) = o yv R)
    (hofin : ∀ yv R, o yv R ≠ ⊤)
    (f : (Tw × Msg → Y) → ℝ≥0∞) (hf1 : ∀ H, f H ≤ 1) (q : ℕ)
    (hf : Tight.TightAvgBound (fun H ↦ (f H).toReal) q) :
    ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          (o (tvals c R xs) R * f R) ≤
      ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
          ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
            (o (yvals c ys) R * f R) +
        ENNReal.ofReal (8 * (q : ℝ) ^ 2 / Fintype.card Msg) *
          ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
            ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
              o (yvals c ys) R := by
  classical
  set κ : ℝ≥0∞ := (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
    (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹) with hκ
  have hκfin : κ ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ (ENNReal.mul_ne_top ?_ ?_) <;>
      exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hr := ud_coupling_real c o h1 (fun a H ↦ a * f H)
  have hi := ud_coupling_ideal (Msg := Msg) (fun ys R ↦ o (yvals c ys) R * f R)
  have hw := ud_coupling_ideal (Msg := Msg) (fun ys R ↦ o (yvals c ys) R)
  rw [← hr, ← hi, ← hw]
  -- the real-valued tight bound
  set Ω := (Tw → Msg) × ((Tw → Y) × (Tw × Msg → Y))
  let w' : (Tw → Y) × (Tw × Msg → Y) → ℝ := fun v ↦ (κ * o (yvals c v.1) v.2).toReal
  let w : Ω → ℝ := fun ω ↦ w' ω.2
  have hw0 : ∀ ω, 0 ≤ w ω := fun _ ↦ ENNReal.toReal_nonneg
  have hS : ∀ x : Tw × Msg, ∑ a : Tw → Msg, (if x ∈ udgMarked c a then (1 : ℝ) else 0) ≤
      (Fintype.card Msg : ℝ)⁻¹ * Fintype.card (Tw → Msg) := by
    intro x
    rw [← Tight.sum_udMarked_real x]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    by_cases hx : x ∈ udgMarked c a
    · have : x ∈ udMarked a := by
        simp only [udgMarked, udMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      simp [hx, this]
    · rw [if_neg hx]
      split_ifs <;> norm_num
  have hH : ∀ (v : (Tw → Y) × (Tw × Msg → Y)) (k : Tw × Msg),
      ∑ ω : Ω with ω.2 = v ∧ k ∈ udgMarked c ω.1, w ω ≤
        (Fintype.card Msg : ℝ)⁻¹ * ∑ ω : Ω with ω.2 = v, w ω := by
    intro v k
    have h := Tight.hidden_indep_real (w' v) _ ENNReal.toReal_nonneg (udgMarked c) hS v k
    have e1 : ∑ ω : Ω with ω.2 = v ∧ k ∈ udgMarked c ω.1, w ω =
        ∑ ω : Ω with ω.2 = v ∧ k ∈ udgMarked c ω.1, w' v :=
      Finset.sum_congr rfl fun ω hω ↦ by
        change w' ω.2 = w' v
        rw [(Finset.mem_filter.1 hω).2.1]
    have e2 : ∑ ω : Ω with ω.2 = v, w ω = ∑ ω : Ω with ω.2 = v, w' v :=
      Finset.sum_congr rfl fun ω hω ↦ by
        change w' ω.2 = w' v
        rw [(Finset.mem_filter.1 hω).2]
    rw [e1, e2]
    exact h
  have hdiff : ∀ (ω : Ω) (k : Tw × Msg), udRep c ω.1 ω.2.1 ω.2.2 k ≠ ω.2.2 k →
      k ∈ udgMarked c ω.1 := by
    intro ω k h
    simp only [udgMarked, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hne
    exact h (by simp [udRep, hne])
  have ht := Tight.tight_view_of (Ω := Ω) w hw0 (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (fun _ ↦ le_rfl) (fun ω ↦ ω.2) (fun ω ↦ udgMarked c ω.1) (Fintype.card Msg : ℝ)⁻¹
    (by positivity) hH q (fun _ H ↦ (f H).toReal) (fun _ ↦ hf)
    (fun ω ↦ udRep c ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2) hdiff
  simp only [mul_one] at ht
  have hreal : ∑ ω : Ω, w ω * (f (udRep c ω.1 ω.2.1 ω.2.2)).toReal ≤
      ∑ ω : Ω, w ω * (f ω.2.2).toReal +
        8 * (q : ℝ) ^ 2 * (Fintype.card Msg : ℝ)⁻¹ * ∑ ω : Ω, w ω := by
    have := (abs_le.1 ht).2
    linarith
  -- back to `ℝ≥0∞`
  have hfin : ∀ ω : Ω, κ * o (yvals c ω.2.1) ω.2.2 ≠ ⊤ :=
    fun ω ↦ ENNReal.mul_ne_top hκfin (hofin _ _)
  have hffin : ∀ H, f H ≠ ⊤ := fun H ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 H)
  have eterm : ∀ (ω : Ω) (H : Tw × Msg → Y),
      κ * (o (yvals c ω.2.1) ω.2.2 * f H) = ENNReal.ofReal (w ω * (f H).toReal) := by
    intro ω H
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin ω),
      ENNReal.ofReal_toReal (hffin H), hκ]
    ring
  have eW : ∑ ω : Ω, κ * o (yvals c ω.2.1) ω.2.2 = ENNReal.ofReal (∑ ω : Ω, w ω) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ hw0 ω]
    exact Finset.sum_congr rfl fun ω _ ↦ (ENNReal.ofReal_toReal (hfin ω)).symm
  have eL : ∑ ω : Ω, κ * (o (yvals c ω.2.1) ω.2.2 * f (udRep c ω.1 ω.2.1 ω.2.2)) =
      ENNReal.ofReal (∑ ω : Ω, w ω * (f (udRep c ω.1 ω.2.1 ω.2.2)).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ mul_nonneg (hw0 ω) ENNReal.toReal_nonneg]
    exact Finset.sum_congr rfl fun ω _ ↦ eterm ω _
  have eI : ∑ ω : Ω, κ * (o (yvals c ω.2.1) ω.2.2 * f ω.2.2) =
      ENNReal.ofReal (∑ ω : Ω, w ω * (f ω.2.2).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ mul_nonneg (hw0 ω) ENNReal.toReal_nonneg]
    exact Finset.sum_congr rfl fun ω _ ↦ eterm ω _
  rw [eL, eI, eW]
  have h8 : (0 : ℝ) ≤ 8 * (q : ℝ) ^ 2 / Fintype.card Msg := by positivity
  rw [← ENNReal.ofReal_mul h8,
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun ω _ ↦ mul_nonneg (hw0 ω) ENNReal.toReal_nonneg)
      (mul_nonneg h8 (Finset.sum_nonneg fun ω _ ↦ hw0 ω))]
  refine ENNReal.ofReal_le_ofReal (le_trans hreal (le_of_eq ?_))
  rw [div_eq_mul_inv]

/-- **Pullback of the tight hidden-set bound along a local map of oracles** (same locality
hypothesis as `HybridModel.pullback`). -/
theorem wq_tightAvgBound_pullback {X X' Y Y' : Type} [Fintype X] [DecidableEq X] [Fintype X']
    [DecidableEq X'] (f : (X → Y) → ℝ) (q : ℕ) (hf : Tight.TightAvgBound f q) (ι : X' ↪ X)
    (φ : (X' → Y') → X → Y)
    (hφ : ∀ H G x, φ H x ≠ φ G x → ∃ x', ι x' = x ∧ H x' ≠ G x') :
    Tight.TightAvgBound (fun H ↦ f (φ H)) q := by
  classical
  intro J _ w hw Hs G S hS ε hε0 hε
  refine hf J w hw (fun s ↦ φ (Hs s)) (φ G) (fun s ↦ (S s).map ι) ?_ ε hε0 ?_
  · intro s k hk
    obtain ⟨x', rfl, hne⟩ := hφ _ _ k hk
    exact Finset.mem_map_of_mem ι (hS s x' hne)
  · intro k
    by_cases hk : ∃ x', ι x' = k
    · obtain ⟨x', rfl⟩ := hk
      refine le_trans (le_of_eq (Finset.sum_congr ?_ fun _ _ ↦ rfl)) (hε x')
      ext s
      simp
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun s hs ↦ ?_) hε0
      obtain ⟨x', -, hx'⟩ := Finset.mem_map.1 (Finset.mem_filter.1 hs).2
      exact (hk ⟨x', hx'⟩).elim

end

end PQ.QROM

#print axioms PQ.QROM.ud_tight_obs_real_le_ideal_add
#print axioms PQ.QROM.wq_tightAvgBound_pullback
