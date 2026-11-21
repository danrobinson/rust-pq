import PQ.QROM.Preimage
import PQ.QROM.Hybrid

/-!
# Multi-target, distinct-tweak bounds for a random tweakable hash against quantum queries

A tweakable hash is modelled as a uniformly random function `H : T × Msg → Y` (`T` the tweaks,
including public seed and address; `Msg` the inputs; `N = |Y|`).  The adversary has quantum access
to `H` and makes at most `q` queries.

All games are ONE-SHOT: a target is fixed for EVERY tweak `t : T` up front and the adversary may
attack any one of them.  Such a game dominates the adaptive multi-target games in which the
adversary selects (adaptively, classically) a subset of distinct tweaks and receives one target for
each selected tweak: an adaptive adversary is simulated by a one-shot adversary that is handed all
targets and ignores those it did not select.  (That domination is not formalised here.)  The bounds
do not depend on `|T|`, the number of targets.

* `mt_preimage_uniform_le` (MT-PRE, uniform targets): `y : T → Y` uniform and independent of `H`;
  win iff the output `(t, x)` satisfies `H (t, x) = y t`.  Bound `(2q+1)² / N`.
* `mt_preimage_planted_le` (MT-PRE, planted targets): `x* : T → Msg` uniform, `y t = H (t, x* t)`;
  win iff `H (t, x) = y t`.  Bound `(2q+1)² (1/N + 1/|Msg|)`.
* `mt_spr_fixed_le` (MT-SPR / TCR, fixed targets): for every fixed `tgt : T → Msg` (not sampled;
  any target assignment that does not depend on `H`), win iff `x ≠ tgt t` and
  `H (t, x) = H (t, tgt t)`.  Bound `(2q+1)² / N`.  `mt_spr_uniform_le`: the same for uniformly
  random targets.
* `*_program_le`: the same statements for arbitrary VCVio quantum query programs
  (`HybridModel.ofProgram`), as explicit uniform averages of `qprob`.

## The couplings (classical facts used)

Worlds are functions `τ : T × Msg → Y × NZ Y` (plus the challenger's other randomness); the real
function is `H = Prod.fst ∘ τ` (`sum_fst_comp`: averaging over `τ` is averaging over `H`), and the
second components are resampling offsets.  With `y_t` the target image of the tweak `t`, the
hybrid function `G` moves every marked value `H (t, x) = y_t` to `y_t + offset ≠ y_t`
(`resample`).  The one classical fact about a coordinate is `resample_fiber`: under a uniform
`(h, d) : Y × NZ Y`, the events `h = y` and `resample y (h, d) = z` are independent and the former
has probability `1/N`.  `sum_marked_dep` / `sum_marked_view` lift it to function space, also when
the target value `y` depends on the other coordinates of `τ`:

  given the view (hybrid function `G` and any data not depending on the coordinate `k`), the point
  `k` is marked with probability exactly `1/N`.

* uniform targets: condition on `y`; every point is marked with probability `1/N` given `(y, G)`.
* fixed targets: `y_t = H (t, tgt t)`, the target coordinates are not resampled and not marked;
  every other point is marked with probability `1/N` given `G`.
* planted targets: `y_t = H (t, x*_t)`, all marked points (the planted ones included) are
  resampled.  Given the view `(y, G)`, the point `(t, x)` is the planted point of `t` with
  probability `1/|Msg|` (the law of the view does not depend on `x*_t`) and is otherwise marked
  with probability `1/N`.

`search_engine` packages the passage from the uniform experiment to `Hidden.search_le`.

Single-function corollaries of the same engine (no tweaks): `spr_fixed_le`, `spr_uniform_le`
(second-preimage resistance, bound `(2q+1)² / N`) and their program-level forms.  (Single-function
preimage resistance is `PQ/QROM/Preimage.lean`.)
-/

open ENNReal Finset

universe u v w

namespace PQ.QROM

theorem natCast_mul_inv_le_one (n : ℕ) : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact le_of_eq (natCast_mul_inv_cancel h.ne')

section Engine

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- **Coupling fact, general form.**  Let the target value `u τ` and `Φ z τ` not depend on the
coordinate `k` of `τ`.  Then, under a sum over `τ` that sees `τ k` only through its resampled value
`resample (u τ) (τ k)`, the indicator "`k` is marked" can be replaced by the constant `1/|Y|`. -/
theorem sum_marked_dep (k : X) (u : (X → Y × NZ Y) → Y)
    (hu : ∀ τ t, u (Function.update τ k t) = u τ)
    (Φ : Y → (X → Y × NZ Y) → ℝ≥0∞) (hΦ : ∀ z τ t, Φ z (Function.update τ k t) = Φ z τ) :
    ∑ τ : X → Y × NZ Y,
        (if (τ k).1 = u τ then (1 : ℝ≥0∞) else 0) * Φ (resample (u τ) (τ k)) τ =
      (Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ τ : X → Y × NZ Y, Φ (resample (u τ) (τ k)) τ := by
  have hL : ∀ τ : X → Y × NZ Y,
      (if (τ k).1 = u τ then (1 : ℝ≥0∞) else 0) * Φ (resample (u τ) (τ k)) τ =
        ∑ y : Y, (if (τ k).1 = y then (1 : ℝ≥0∞) else 0) *
          ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) := by
    intro τ
    rw [Finset.sum_eq_single (u τ)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : ∀ τ : X → Y × NZ Y,
      (Fintype.card Y : ℝ≥0∞)⁻¹ * Φ (resample (u τ) (τ k)) τ =
        ∑ y : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
          ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) := by
    intro τ
    rw [Finset.sum_eq_single (u τ)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∑ τ : X → Y × NZ Y,
        (if (τ k).1 = u τ then (1 : ℝ≥0∞) else 0) * Φ (resample (u τ) (τ k)) τ
      = ∑ y : Y, ∑ τ : X → Y × NZ Y, (if (τ k).1 = y then (1 : ℝ≥0∞) else 0) *
          ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) :=
        (Finset.sum_congr rfl fun τ _ ↦ hL τ).trans Finset.sum_comm
    _ = ∑ y : Y, ∑ τ : X → Y × NZ Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
          ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) :=
        Finset.sum_congr rfl fun y _ ↦
          sum_coord_change k (resample y) (resample y)
            (fun t ↦ if t.1 = y then (1 : ℝ≥0∞) else 0)
            (fun _ ↦ (Fintype.card Y : ℝ≥0∞)⁻¹) (resample_fiber y)
            (fun z τ ↦ (if u τ = y then (1 : ℝ≥0∞) else 0) * Φ z τ)
            (by intro z τ t; rw [hu, hΦ])
    _ = ∑ τ : X → Y × NZ Y, (Fintype.card Y : ℝ≥0∞)⁻¹ * Φ (resample (u τ) (τ k)) τ :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun τ _ ↦ (hR τ).symm)
    _ = _ := by rw [Finset.mul_sum]

/-- **Coupling fact, view form.**  Let `G τ` be a hybrid function whose value at `k` is the
resampling of `τ k` away from `u τ`, and whose other values, like `u τ` and the test function
`Ψ τ ·`, do not depend on `τ k`.  Then, given `G` (and `Ψ`), the point `k` is marked with
probability exactly `1/|Y|`. -/
theorem sum_marked_view (k : X) (u : (X → Y × NZ Y) → Y)
    (hu : ∀ τ t, u (Function.update τ k t) = u τ)
    (G : (X → Y × NZ Y) → X → Y) (hGk : ∀ τ, G τ k = resample (u τ) (τ k))
    (hG : ∀ τ t j, j ≠ k → G (Function.update τ k t) j = G τ j)
    (Ψ : (X → Y × NZ Y) → (X → Y) → ℝ≥0∞)
    (hΨ : ∀ τ t g, Ψ (Function.update τ k t) g = Ψ τ g) :
    ∑ τ : X → Y × NZ Y, (if (τ k).1 = u τ then (1 : ℝ≥0∞) else 0) * Ψ τ (G τ) =
      (Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ τ : X → Y × NZ Y, Ψ τ (G τ) := by
  have e := sum_marked_dep k u hu (fun z τ ↦ Ψ τ (Function.update (G τ) k z)) (by
    intro z τ t
    have : Function.update (G (Function.update τ k t)) k z = Function.update (G τ) k z := by
      funext j
      by_cases hj : j = k
      · rw [hj]; simp
      · simp [Function.update_of_ne hj, hG τ t j hj]
    simp only [this, hΨ])
  have hupd : ∀ τ, Function.update (G τ) k (resample (u τ) (τ k)) = G τ := fun τ ↦ by
    rw [← hGk]; exact Function.update_eq_self _ _
  simpa only [hupd] using e

variable {Leaf : Type} {q : ℕ}

/-- **From a uniform experiment to the hidden-set lemma.**  The challenger samples `H` uniformly
and `p : P` uniformly; the adversary receives `a p H`, and wins iff its output lies in the marked
set `W p H`.  In the coupling `H = Prod.fst ∘ τ`, if the hybrid function `G p τ` agrees with `H`
outside the marked set and the marked set is `ε`-hidden from the view `(a p H, G p τ)`, the
winning probability is at most `(2q+1)² ε`. -/
theorem search_engine {P A : Type} [Fintype P] (ε : ℝ≥0∞) (a : P → (X → Y) → A)
    (G : P → (X → Y × NZ Y) → X → Y) (W : P → (X → Y) → Finset X)
    (hidden : ∀ κ : ℝ≥0∞, Hidden (Ω := P × (X → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ (a ω.1 (fun k ↦ (ω.2 k).1), G ω.1 ω.2))
      (fun ω ↦ W ω.1 (fun k ↦ (ω.2 k).1)) ε)
    (hG : ∀ p τ k, (τ k).1 ≠ G p τ k → k ∈ W p (fun k ↦ (τ k).1))
    (hε : Fintype.card Y = 1 → 1 ≤ ε)
    (M : A → HybridModel X Y Leaf q) (out : A → Leaf → X) :
    ∑ H : X → Y, ∑ p : P,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card P : ℝ≥0∞)⁻¹) *
          (M (a p H)).prob H (fun l ↦ out (a p H) l ∈ W p H) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε := by
  have hXY : Fintype.card (X → Y) ≠ 0 := Fintype.card_ne_zero
  set cXY : ℝ≥0∞ := (Fintype.card (X → Y) : ℝ≥0∞) with hcXY
  set cP : ℝ≥0∞ := (Fintype.card P : ℝ≥0∞) with hcP
  have iXY : cXY * cXY⁻¹ = 1 := natCast_mul_inv_cancel hXY
  have iP : cP * cP⁻¹ ≤ 1 := natCast_mul_inv_le_one _
  by_cases hN : Fintype.card Y = 1
  · -- trivial case: the bound is at least one
    have h1 : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε :=
      calc (1 : ℝ≥0∞) = 1 * 1 := (mul_one 1).symm
        _ ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 * ε :=
            mul_le_mul' (one_le_two_mul_add_one_sq q) (hε hN)
    refine le_trans ?_ h1
    calc ∑ H : X → Y, ∑ p : P, (cXY⁻¹ * cP⁻¹) *
            (M (a p H)).prob H (fun l ↦ out (a p H) l ∈ W p H)
        ≤ ∑ _H : X → Y, ∑ _p : P, (cXY⁻¹ * cP⁻¹) * 1 := by
          gcongr with H _ p _
          exact prob_le_one_of_sub (M (a p H)) (out (a p H))
            (fun H' T ↦ (M (a p H)).prob_sub H' (out (a p H)) T) H _
      _ = (cXY * cXY⁻¹) * (cP * cP⁻¹) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcP, hcXY]
          ring
      _ ≤ 1 := by rw [iXY, one_mul]; exact iP
  · have hnt : Nontrivial Y :=
      Fintype.one_lt_card_iff_nontrivial.1
        (by have := Fintype.card_pos (α := Y); omega)
    obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
    have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
    have hXD : Fintype.card (X → NZ Y) ≠ 0 := Fintype.card_ne_zero
    set cXD : ℝ≥0∞ := (Fintype.card (X → NZ Y) : ℝ≥0∞) with hcXD
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
    set κ : ℝ≥0∞ := cP⁻¹ * cXY⁻¹ * cXD⁻¹ with hκ
    have hw : ∑ _ω : P × (X → Y × NZ Y), κ ≤ 1 := by
      rw [Fintype.sum_prod_type]
      have := sum_fst_comp (X := X) (A := Y) (B := NZ Y) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cP * (cXD * (cXY * κ)) = (cP * cP⁻¹) * ((cXY * cXY⁻¹) * (cXD * cXD⁻¹)) := by
            rw [hκ]; ring
        _ ≤ 1 := by rw [iXY, iXD, mul_one, mul_one]; exact iP
    have hs := (hidden κ).search_le hw (fun v ↦ M v.1)
      (fun ω k ↦ (ω.2 k).1) (fun v ↦ v.2) (fun ω k hk ↦ hG ω.1 ω.2 k hk) (fun v ↦ out v.1)
    refine le_trans (le_of_eq ?_) hs
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have e := sum_fst_comp (X := X) (A := Y) (B := NZ Y)
      (fun H ↦ κ * (M (a p H)).prob H (fun l ↦ out (a p H) l ∈ W p H))
    dsimp only at e ⊢
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    calc cXY⁻¹ * cP⁻¹ * (M (a p H)).prob H (fun l ↦ out (a p H) l ∈ W p H)
        = (cXD * cXD⁻¹) *
            (cXY⁻¹ * cP⁻¹ * (M (a p H)).prob H (fun l ↦ out (a p H) l ∈ W p H)) := by
          rw [iXD, one_mul]
      _ = cXD * (κ * (M (a p H)).prob H (fun l ↦ out (a p H) l ∈ W p H)) := by rw [hκ]; ring

end Engine

section Games

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {T Msg : Type} [Fintype T] [DecidableEq T] [Fintype Msg] [DecidableEq Msg]
variable {Leaf : Type} {q : ℕ}

/-! ### MT-PRE, uniform targets -/

/-- Uniform targets: given the view `(y, G)`, every point `(t, x)` is marked (`H (t, x) = y t`)
with probability exactly `1/|Y|`. -/
theorem hidden_mt_uniform (κ : ℝ≥0∞) :
    Hidden (Ω := (T → Y) × (T × Msg → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ (ω.1, fun j ↦ resample (ω.1 j.1) (ω.2 j)))
      (fun ω ↦ univ.filter fun k ↦ (ω.2 k).1 = ω.1 k.1) (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  refine le_of_eq ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have e := sum_marked_view (X := T × Msg) k (fun _ ↦ y k.1) (fun _ _ ↦ rfl)
    (fun τ j ↦ resample (y j.1) (τ j)) (fun _ ↦ rfl)
    (fun τ t j hj ↦ by simp [Function.update_of_ne hj])
    (fun _ g ↦ κ * φ (y, g)) (fun _ _ _ ↦ rfl)
  dsimp only at e ⊢
  rw [← e]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  split_ifs <;> simp

/-- **MT-PRE, uniform targets (HybridModel level).**  Experiment: `H ← (T × Msg → Y)` uniform,
`y ← (T → Y)` uniform (an independent target image for every tweak); the `q`-query algorithm
`M y` runs with quantum access to `H` and outputs `(t, x) = out y p`; it wins iff
`H (t, x) = y t`.  The winning probability is at most `(2q+1)² / |Y|`, whatever `|T|`.

This one-shot game (targets for all tweaks handed over up front) dominates the adaptive game in
which the adversary selects distinct tweaks and receives a target for each. -/
theorem mt_preimage_uniform_le (M : (T → Y) → HybridModel (T × Msg) Y Leaf q)
    (out : (T → Y) → Leaf → T × Msg) :
    ∑ H : T × Msg → Y, ∑ y : T → Y,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T → Y) : ℝ≥0∞)⁻¹) *
          (M y).prob H (fun p ↦ H (out y p) = y (out y p).1) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  have h := search_engine (X := T × Msg) (P := T → Y) (A := T → Y) (Fintype.card Y : ℝ≥0∞)⁻¹
    (fun y _ ↦ y) (fun y τ j ↦ resample (y j.1) (τ j))
    (fun y H ↦ univ.filter fun k ↦ H k = y k.1)
    (fun κ ↦ hidden_mt_uniform κ)
    (by
      intro y τ k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hne
      exact hk (by simp [resample, hne]))
    (by intro hN; simp [hN]) M out
  simpa only [div_eq_mul_inv, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-! ### MT-SPR / TCR, fixed targets -/

/-- The hybrid function for fixed targets: the target coordinates `(t, tgt t)` are kept, every
other point of the tweak `t` is resampled away from `H (t, tgt t)`. -/
def sprG (tgt : T → Msg) (τ : T × Msg → Y × NZ Y) (j : T × Msg) : Y :=
  if j.2 = tgt j.1 then (τ j).1 else resample (τ (j.1, tgt j.1)).1 (τ j)

/-- Fixed targets: given the hybrid function `G`, every non-target point `(t, x)` is marked
(`H (t, x) = H (t, tgt t)`) with probability exactly `1/|Y|`. -/
theorem hidden_mt_spr (tgt : T → Msg) (κ : ℝ≥0∞) :
    Hidden (Ω := Unit × (T × Msg → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ ((), sprG tgt ω.2))
      (fun ω ↦ univ.filter fun k ↦ k.2 ≠ tgt k.1 ∧ (ω.2 k).1 = (ω.2 (k.1, tgt k.1)).1)
      (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  by_cases hk : k.2 = tgt k.1
  · simp [hk]
  · have hk' : (k.1, tgt k.1) ≠ k := fun h ↦ hk (by rw [← h])
    have e := sum_marked_view (X := T × Msg) k (fun τ ↦ (τ (k.1, tgt k.1)).1)
      (fun τ t ↦ by simp [Function.update_of_ne hk'])
      (sprG tgt) (fun τ ↦ by simp [sprG, hk])
      (fun τ t j hj ↦ by
        have hj' : (j.1, tgt j.1) ≠ k := by
          intro h
          apply hk
          rw [← h]
        simp [sprG, Function.update_of_ne hj, Function.update_of_ne hj'])
      (fun _ g ↦ κ * φ ((), g)) (fun _ _ _ ↦ rfl)
    refine le_of_eq ?_
    rw [Finset.mul_sum] at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    simp only [hk, not_false_eq_true, true_and, ne_eq]
    split_ifs <;> simp

/-- **MT-SPR / TCR with fixed targets (HybridModel level).**  For EVERY fixed target assignment
`tgt : T → Msg` (one target input per tweak, not sampled: this covers targets chosen adversarially
but independently of `H`, on which the algorithm `M` may depend arbitrarily): `H ← (T × Msg → Y)`
uniform; the `q`-query algorithm `M` runs with quantum access to `H` and outputs `(t, x) = out p`;
it wins iff `x ≠ tgt t` and `H (t, x) = H (t, tgt t)`.  The winning probability is at most
`(2q+1)² / |Y|`, whatever `|T|`.

This one-shot game dominates the adaptive game in which the adversary commits to targets for a
subset of distinct tweaks. -/
theorem mt_spr_fixed_le (tgt : T → Msg) (M : HybridModel (T × Msg) Y Leaf q)
    (out : Leaf → T × Msg) :
    ∑ H : T × Msg → Y, (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ *
        M.prob H (fun p ↦ (out p).2 ≠ tgt (out p).1 ∧ H (out p) = H ((out p).1, tgt (out p).1)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  have h := search_engine (X := T × Msg) (P := Unit) (A := Unit) (Fintype.card Y : ℝ≥0∞)⁻¹
    (fun _ _ ↦ ()) (fun _ τ ↦ sprG tgt τ)
    (fun _ H ↦ univ.filter fun k ↦ k.2 ≠ tgt k.1 ∧ H k = H (k.1, tgt k.1))
    (by intro κ; have := hidden_mt_spr (Y := Y) tgt κ; exact this)
    (by
      intro _ τ k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h2 : k.2 = tgt k.1
      · exact (hk (by simp [sprG, h2])).elim
      · refine ⟨h2, ?_⟩
        by_contra hne
        exact hk (by simp [sprG, h2, resample, hne]))
    (by intro hN; simp [hN]) (fun _ ↦ M) (fun _ ↦ out)
  simpa only [div_eq_mul_inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.univ_unique,
    Finset.sum_singleton, Fintype.card_unit, Nat.cast_one, inv_one, mul_one] using h

/-- **MT-SPR / TCR with uniformly random targets (HybridModel level).**  `H` uniform,
`tgt ← (T → Msg)` uniform; the algorithm `M tgt` outputs `(t, x)` and wins iff `x ≠ tgt t` and
`H (t, x) = H (t, tgt t)`.  Bound `(2q+1)² / |Y|`. -/
theorem mt_spr_uniform_le (M : (T → Msg) → HybridModel (T × Msg) Y Leaf q)
    (out : (T → Msg) → Leaf → T × Msg) :
    ∑ H : T × Msg → Y, ∑ tgt : T → Msg,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T → Msg) : ℝ≥0∞)⁻¹) *
          (M tgt).prob H (fun p ↦ (out tgt p).2 ≠ tgt (out tgt p).1 ∧
            H (out tgt p) = H ((out tgt p).1, tgt (out tgt p).1)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  set B : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) with hB
  set cP : ℝ≥0∞ := (Fintype.card (T → Msg) : ℝ≥0∞) with hcP
  rw [Finset.sum_comm]
  calc ∑ tgt : T → Msg, ∑ H : T × Msg → Y,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * cP⁻¹) *
          (M tgt).prob H (fun p ↦ (out tgt p).2 ≠ tgt (out tgt p).1 ∧
            H (out tgt p) = H ((out tgt p).1, tgt (out tgt p).1))
      = ∑ tgt : T → Msg, cP⁻¹ * ∑ H : T × Msg → Y,
          (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ *
            (M tgt).prob H (fun p ↦ (out tgt p).2 ≠ tgt (out tgt p).1 ∧
              H (out tgt p) = H ((out tgt p).1, tgt (out tgt p).1)) := by
        refine Finset.sum_congr rfl fun tgt _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun H _ ↦ by ring
    _ ≤ ∑ _tgt : T → Msg, cP⁻¹ * B := by
        gcongr with tgt _
        exact mt_spr_fixed_le tgt (M tgt) (out tgt)
    _ = (cP * cP⁻¹) * B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcP]
        ring
    _ ≤ 1 * B := by
        gcongr
        exact natCast_mul_inv_le_one _
    _ = B := one_mul _

/-! ### MT-PRE, planted targets -/

/-- Planted targets: `y t = H (t, x* t)`.  Given the view `(y, G)`, the point `(t, x)` is the
planted point of the tweak `t` with probability `1/|Msg|` and is otherwise marked with probability
`1/|Y|`. -/
theorem hidden_mt_planted (κ : ℝ≥0∞) :
    Hidden (Ω := (T → Msg) × (T × Msg → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ (fun t ↦ (ω.2 (t, ω.1 t)).1,
        fun j ↦ resample (ω.2 (j.1, ω.1 j.1)).1 (ω.2 j)))
      (fun ω ↦ univ.filter fun k ↦ (ω.2 k).1 = (ω.2 (k.1, ω.1 k.1)).1)
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  intro k φ
  obtain ⟨t, x⟩ := k
  set cN : ℝ≥0∞ := (Fintype.card Y : ℝ≥0∞) with hcN
  set cM : ℝ≥0∞ := (Fintype.card Msg : ℝ≥0∞) with hcM
  -- the view
  let V : (T → Msg) → (T × Msg → Y × NZ Y) → (T → Y) × (T × Msg → Y) := fun xs τ ↦
    (fun t' ↦ (τ (t', xs t')).1, fun j ↦ resample (τ (j.1, xs j.1)).1 (τ j))
  -- the view with the target image of the tweak `t` replaced by `y`
  let yv : Y → (T → Msg) → (T × Msg → Y × NZ Y) → T → Y := fun y xs τ t' ↦
    if t' = t then y else (τ (t', xs t')).1
  let V' : Y → (T → Msg) → (T × Msg → Y × NZ Y) → (T → Y) × (T × Msg → Y) := fun y xs τ ↦
    (yv y xs τ, fun j ↦ resample (yv y xs τ j.1) (τ j))
  let A : (T → Msg) → ℝ≥0∞ := fun xs ↦ ∑ τ : T × Msg → Y × NZ Y, φ (V xs τ)
  let B : (T → Msg) → ℝ≥0∞ := fun xs ↦ ∑ y : Y, ∑ τ : T × Msg → Y × NZ Y, φ (V' y xs τ)
  have hyv : ∀ xs τ, yv (τ (t, xs t)).1 xs τ = fun t' ↦ (τ (t', xs t')).1 := by
    intro xs τ
    funext t'
    by_cases h : t' = t
    · simp [yv, h]
    · simp [yv, h]
  have hA : ∀ xs, A xs = cN⁻¹ * B xs := by
    intro xs
    have h1 : A xs = ∑ τ : T × Msg → Y × NZ Y, φ (V' (τ (t, xs t)).1 xs τ) := by
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      simp only [V, V', hyv]
    rw [h1, sum_split_value (t, xs t) fun y τ ↦ φ (V' y xs τ)]
    show _ = cN⁻¹ * ∑ y : Y, ∑ τ : T × Msg → Y × NZ Y, φ (V' y xs τ)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hupd : ∀ (τ : T × Msg → Y × NZ Y) (v : Y × NZ Y),
        yv y xs (Function.update τ (t, xs t) v) = yv y xs τ := by
      intro τ v
      funext t'
      by_cases h : t' = t
      · simp [yv, h]
      · have : (t', xs t') ≠ (t, xs t) := fun h' ↦ h (congrArg Prod.fst h')
        simp [yv, h]
    exact sum_marked_view (X := T × Msg) (t, xs t) (fun _ ↦ y) (fun _ _ ↦ rfl)
      (fun τ j ↦ resample (yv y xs τ j.1) (τ j)) (fun τ ↦ by simp [yv])
      (fun τ v j hj ↦ by simp only [hupd, Function.update_of_ne hj])
      (fun τ g ↦ φ (yv y xs τ, g)) (fun τ v g ↦ by simp only [hupd])
  have hBinv : ∀ (z : Unit) (xs : T → Msg) (m : Msg),
      (fun (_ : Unit) xs ↦ B xs) z (Function.update xs t m) = (fun (_ : Unit) xs ↦ B xs) z xs := by
    intro _ xs m
    have : ∀ y τ, yv y (Function.update xs t m) τ = yv y xs τ := by
      intro y τ
      funext t'
      by_cases h : t' = t
      · simp [yv, h]
      · simp [yv, h]
    simp only [B, V', this]
  have hplant : ∑ xs : T → Msg, (if xs t = x then A xs else 0) = cM⁻¹ * ∑ xs : T → Msg, A xs := by
    have e := sum_coord_change t (fun _ : Msg ↦ ()) (fun _ : Msg ↦ ())
      (fun m ↦ if m = x then (1 : ℝ≥0∞) else 0) (fun _ ↦ cM⁻¹)
      (by
        intro z
        have : Nonempty Msg := ⟨x⟩
        simp only [Finset.filter_true_of_mem, Finset.mem_univ, implies_true, Finset.sum_ite_eq',
          ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact (natCast_mul_inv_cancel Fintype.card_ne_zero).symm)
      (fun _ xs ↦ B xs) hBinv
    calc ∑ xs : T → Msg, (if xs t = x then A xs else 0)
        = ∑ xs : T → Msg, cN⁻¹ * ((if xs t = x then (1 : ℝ≥0∞) else 0) * B xs) := by
          refine Finset.sum_congr rfl fun xs _ ↦ ?_
          rw [hA]
          split_ifs <;> simp
      _ = cN⁻¹ * ∑ xs : T → Msg, cM⁻¹ * B xs := by rw [← Finset.mul_sum, e]
      _ = cM⁻¹ * ∑ xs : T → Msg, A xs := by
          simp only [hA, ← Finset.mul_sum]
          ring
  have hT : ∀ xs : T → Msg, ∑ τ : T × Msg → Y × NZ Y,
      (if (τ (t, x)).1 = (τ (t, xs t)).1 then φ (V xs τ) else 0) ≤
        (if xs t = x then A xs else 0) + cN⁻¹ * A xs := by
    intro xs
    by_cases hx : xs t = x
    · simp only [hx, ite_true]
      refine le_trans (Finset.sum_le_sum fun τ _ ↦ ?_) le_self_add
      exact le_rfl
    · simp only [hx, ite_false, zero_add]
      have hk' : (t, xs t) ≠ (t, x) := fun h ↦ hx (congrArg Prod.snd h)
      have hj' : ∀ j : T × Msg, (j.1, xs j.1) ≠ (t, x) := by
        intro j h
        have h1 : j.1 = t := congrArg Prod.fst h
        have h2 : xs j.1 = x := congrArg Prod.snd h
        exact hx (h1 ▸ h2)
      have e := sum_marked_view (X := T × Msg) (t, x) (fun τ ↦ (τ (t, xs t)).1)
        (fun τ v ↦ by simp [Function.update_of_ne hk'])
        (fun τ j ↦ resample (τ (j.1, xs j.1)).1 (τ j)) (fun _ ↦ rfl)
        (fun τ v j hj ↦ by simp [Function.update_of_ne hj, Function.update_of_ne (hj' j)])
        (fun τ g ↦ φ (fun t' ↦ (τ (t', xs t')).1, g))
        (fun τ v g ↦ by
          have : ∀ t', (t', xs t') ≠ (t, x) := fun t' ↦ hj' (t', x)
          simp [Function.update_of_ne (this _)])
      refine le_of_eq ?_
      show _ = cN⁻¹ * ∑ τ : T × Msg → Y × NZ Y, φ (V xs τ)
      rw [← e]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      split_ifs <;> simp [V]
  have hL : ∑ ω : (T → Msg) × (T × Msg → Y × NZ Y),
      κ * (if (t, x) ∈ univ.filter (fun k : T × Msg ↦ (ω.2 k).1 = (ω.2 (k.1, ω.1 k.1)).1)
        then φ (fun t ↦ (ω.2 (t, ω.1 t)).1, fun j ↦ resample (ω.2 (j.1, ω.1 j.1)).1 (ω.2 j))
        else 0) =
      κ * ∑ xs : T → Msg, ∑ τ : T × Msg → Y × NZ Y,
        (if (τ (t, x)).1 = (τ (t, xs t)).1 then φ (V xs τ) else 0) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mul_sum, V]
  have hR : ∑ ω : (T → Msg) × (T × Msg → Y × NZ Y),
      κ * φ (fun t ↦ (ω.2 (t, ω.1 t)).1, fun j ↦ resample (ω.2 (j.1, ω.1 j.1)).1 (ω.2 j)) =
      κ * ∑ xs : T → Msg, A xs := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, A, V]
  rw [hL, hR]
  calc κ * ∑ xs : T → Msg, ∑ τ : T × Msg → Y × NZ Y,
        (if (τ (t, x)).1 = (τ (t, xs t)).1 then φ (V xs τ) else 0)
      ≤ κ * ∑ xs : T → Msg, ((if xs t = x then A xs else 0) + cN⁻¹ * A xs) := by
        gcongr with xs _
        exact hT xs
    _ = κ * (cM⁻¹ * ∑ xs : T → Msg, A xs + cN⁻¹ * ∑ xs : T → Msg, A xs) := by
        rw [Finset.sum_add_distrib, hplant, ← Finset.mul_sum]
    _ = (cN⁻¹ + cM⁻¹) * (κ * ∑ xs : T → Msg, A xs) := by ring

/-- **MT-PRE, planted targets (HybridModel level; the real PRE game shape).**  Experiment:
`H ← (T × Msg → Y)` uniform, `x* ← (T → Msg)` uniform (an independent planted input for every
tweak), `y t := H (t, x* t)`; the `q`-query algorithm `M y` runs with quantum access to `H` and
outputs `(t, x) = out y p`; it wins iff `H (t, x) = y t`.  The winning probability is at most
`(2q+1)² (1/|Y| + 1/|Msg|)`, whatever `|T|`.

This one-shot game dominates the adaptive game in which the adversary selects distinct tweaks and
receives the image of a fresh planted input for each. -/
theorem mt_preimage_planted_le (M : (T → Y) → HybridModel (T × Msg) Y Leaf q)
    (out : (T → Y) → Leaf → T × Msg) :
    ∑ H : T × Msg → Y, ∑ xs : T → Msg,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T → Msg) : ℝ≥0∞)⁻¹) *
          (M (fun t ↦ H (t, xs t))).prob H
            (fun p ↦ H (out (fun t ↦ H (t, xs t)) p) =
              H ((out (fun t ↦ H (t, xs t)) p).1, xs (out (fun t ↦ H (t, xs t)) p).1)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  have h := search_engine (X := T × Msg) (P := T → Msg) (A := T → Y)
    ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹)
    (fun xs H t ↦ H (t, xs t)) (fun xs τ j ↦ resample (τ (j.1, xs j.1)).1 (τ j))
    (fun xs H ↦ univ.filter fun k ↦ H k = H (k.1, xs k.1))
    (fun κ ↦ hidden_mt_planted κ)
    (by
      intro xs τ k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hne
      exact hk (by simp [resample, hne]))
    (by intro hN; simp [hN]) M out
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

end Games

/-! ### Single function: second-preimage resistance -/

section Single

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Leaf : Type} {q : ℕ}

/-- The hybrid function for a single fixed target: `tgt` is kept, every other point is resampled
away from `H tgt`. -/
def sprG₁ (tgt : X) (τ : X → Y × NZ Y) (j : X) : Y :=
  if j = tgt then (τ j).1 else resample (τ tgt).1 (τ j)

/-- Single fixed target: given the hybrid function, every point `k ≠ tgt` is marked
(`H k = H tgt`) with probability exactly `1/|Y|`. -/
theorem hidden_spr (tgt : X) (κ : ℝ≥0∞) :
    Hidden (Ω := Unit × (X → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ ((), sprG₁ tgt ω.2))
      (fun ω ↦ univ.filter fun k ↦ k ≠ tgt ∧ (ω.2 k).1 = (ω.2 tgt).1)
      (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  by_cases hk : k = tgt
  · simp [hk]
  · have e := sum_marked_view k (fun τ : X → Y × NZ Y ↦ (τ tgt).1)
      (fun τ t ↦ by simp [Function.update_of_ne (Ne.symm hk)])
      (sprG₁ tgt) (fun τ ↦ by simp [sprG₁, hk])
      (fun τ t j hj ↦ by
        simp [sprG₁, Function.update_of_ne hj, Function.update_of_ne (Ne.symm hk)])
      (fun _ g ↦ κ * φ ((), g)) (fun _ _ _ ↦ rfl)
    refine le_of_eq ?_
    rw [Finset.mul_sum] at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    simp only [hk, not_false_eq_true, true_and, ne_eq]
    split_ifs <;> simp

/-- **Second-preimage resistance of a random function, fixed target (HybridModel level).**  For
every fixed `tgt : X` (not sampled; the algorithm may depend on it): `H ← (X → Y)` uniform; the
`q`-query algorithm `M` outputs `out p` and wins iff `out p ≠ tgt` and `H (out p) = H tgt`.  The
winning probability is at most `(2q+1)² / |Y|`. -/
theorem spr_fixed_le (tgt : X) (M : HybridModel X Y Leaf q) (out : Leaf → X) :
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        M.prob H (fun p ↦ out p ≠ tgt ∧ H (out p) = H tgt) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  have h := search_engine (X := X) (P := Unit) (A := Unit) (Fintype.card Y : ℝ≥0∞)⁻¹
    (fun _ _ ↦ ()) (fun _ τ ↦ sprG₁ tgt τ)
    (fun _ H ↦ univ.filter fun k ↦ k ≠ tgt ∧ H k = H tgt)
    (by intro κ; have := hidden_spr (Y := Y) tgt κ; exact this)
    (by
      intro _ τ k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h2 : k = tgt
      · exact (hk (by simp [sprG₁, h2])).elim
      · refine ⟨h2, ?_⟩
        by_contra hne
        exact hk (by simp [sprG₁, h2, resample, hne]))
    (by intro hN; simp [hN]) (fun _ ↦ M) (fun _ ↦ out)
  simpa only [div_eq_mul_inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.univ_unique,
    Finset.sum_singleton, Fintype.card_unit, Nat.cast_one, inv_one, mul_one] using h

/-- **Second-preimage resistance of a random function, uniform target (HybridModel level).**
`H ← (X → Y)` uniform, `tgt ← X` uniform; the algorithm `M tgt` wins iff its output `x'` satisfies
`x' ≠ tgt` and `H x' = H tgt`.  Bound `(2q+1)² / |Y|`. -/
theorem spr_uniform_le (M : X → HybridModel X Y Leaf q) (out : X → Leaf → X) :
    ∑ H : X → Y, ∑ tgt : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          (M tgt).prob H (fun p ↦ out tgt p ≠ tgt ∧ H (out tgt p) = H tgt) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  set B : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) with hB
  set cP : ℝ≥0∞ := (Fintype.card X : ℝ≥0∞) with hcP
  rw [Finset.sum_comm]
  calc ∑ tgt : X, ∑ H : X → Y, ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * cP⁻¹) *
          (M tgt).prob H (fun p ↦ out tgt p ≠ tgt ∧ H (out tgt p) = H tgt)
      = ∑ tgt : X, cP⁻¹ * ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
            (M tgt).prob H (fun p ↦ out tgt p ≠ tgt ∧ H (out tgt p) = H tgt) := by
        refine Finset.sum_congr rfl fun tgt _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun H _ ↦ by ring
    _ ≤ ∑ _tgt : X, cP⁻¹ * B := by
        gcongr with tgt _
        exact spr_fixed_le tgt (M tgt) (out tgt)
    _ = (cP * cP⁻¹) * B := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcP]
        ring
    _ ≤ 1 * B := by
        gcongr
        exact natCast_mul_inv_le_one _
    _ = B := one_mul _

end Single

/-! ### Program-level statements -/

section Programs

open Quantum

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {T Msg : Type} [Fintype T] [DecidableEq T] [Fintype Msg] [DecidableEq Msg]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **MT-PRE, uniform targets, for quantum query programs.**  `H ← (T × Msg → Y)` uniform,
`y ← (T → Y)` uniform; the program `x y` (any VCVio quantum query program with at most `q` oracle
calls on every path, depending arbitrarily on the whole target vector, from any initial substate
`ρ y`) runs with quantum access to `H`; `out y` decodes its leaf to `(t, x)`; it wins iff
`H (t, x) = y t`.  The winning probability is at most `(2q+1)² / |Y|`, whatever `|T|`. -/
theorem mt_preimage_uniform_program_le (I : L.Interp)
    (x : (T → Y) → QuantumComp L (qromSpec (T × Msg) Y) W A) (ρ : (T → Y) → SubState A) (q : ℕ)
    (hx : ∀ y, QueryBounded (x y) q) (out : (T → Y) → (Σ u, W u) → T × Msg) :
    ∑ H : T × Msg → Y, ∑ y : T → Y,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T → Y) : ℝ≥0∞)⁻¹) *
          qprob I H (x y) (ρ y) (fun p ↦ H (out y p) = y (out y p).1) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  mt_preimage_uniform_le
    (fun y ↦ HybridModel.ofProgram I (x y) (ρ y) q (hx y) (out y)) (fun _ ↦ id)

/-- **MT-PRE, planted targets, for quantum query programs.**  `H ← (T × Msg → Y)` uniform,
`x* ← (T → Msg)` uniform, `y t := H (t, x* t)`; the program `x y` (at most `q` oracle calls on
every path) runs with quantum access to `H`; `out y` decodes its leaf to `(t, x)`; it wins iff
`H (t, x) = y t`.  The winning probability is at most `(2q+1)² (1/|Y| + 1/|Msg|)`. -/
theorem mt_preimage_planted_program_le (I : L.Interp)
    (x : (T → Y) → QuantumComp L (qromSpec (T × Msg) Y) W A) (ρ : (T → Y) → SubState A) (q : ℕ)
    (hx : ∀ y, QueryBounded (x y) q) (out : (T → Y) → (Σ u, W u) → T × Msg) :
    ∑ H : T × Msg → Y, ∑ xs : T → Msg,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T → Msg) : ℝ≥0∞)⁻¹) *
          qprob I H (x (fun t ↦ H (t, xs t))) (ρ (fun t ↦ H (t, xs t)))
            (fun p ↦ H (out (fun t ↦ H (t, xs t)) p) =
              H ((out (fun t ↦ H (t, xs t)) p).1, xs (out (fun t ↦ H (t, xs t)) p).1)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) :=
  mt_preimage_planted_le
    (fun y ↦ HybridModel.ofProgram I (x y) (ρ y) q (hx y) (out y)) (fun _ ↦ id)

/-- **MT-SPR / TCR with fixed targets, for quantum query programs.**  For every fixed
`tgt : T → Msg` and every program `x` with at most `q` oracle calls on every path (it may depend
on `tgt`): `H ← (T × Msg → Y)` uniform; `out` decodes the leaf to `(t, x)`; the program wins iff
`x ≠ tgt t` and `H (t, x) = H (t, tgt t)`.  The winning probability is at most `(2q+1)² / |Y|`. -/
theorem mt_spr_fixed_program_le (tgt : T → Msg) (I : L.Interp)
    (x : QuantumComp L (qromSpec (T × Msg) Y) W A) (ρ : SubState A) (q : ℕ)
    (hx : QueryBounded x q) (out : (Σ u, W u) → T × Msg) :
    ∑ H : T × Msg → Y, (Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ *
        qprob I H x ρ
          (fun p ↦ (out p).2 ≠ tgt (out p).1 ∧ H (out p) = H ((out p).1, tgt (out p).1)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  mt_spr_fixed_le tgt (HybridModel.ofProgram I x ρ q hx out) id

/-- **MT-SPR / TCR with uniformly random targets, for quantum query programs.**  `H` uniform,
`tgt ← (T → Msg)` uniform; the program `x tgt` (at most `q` oracle calls on every path) wins iff
its decoded output `(t, x)` satisfies `x ≠ tgt t` and `H (t, x) = H (t, tgt t)`.  Bound
`(2q+1)² / |Y|`. -/
theorem mt_spr_uniform_program_le (I : L.Interp)
    (x : (T → Msg) → QuantumComp L (qromSpec (T × Msg) Y) W A) (ρ : (T → Msg) → SubState A)
    (q : ℕ) (hx : ∀ tgt, QueryBounded (x tgt) q) (out : (T → Msg) → (Σ u, W u) → T × Msg) :
    ∑ H : T × Msg → Y, ∑ tgt : T → Msg,
        ((Fintype.card (T × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (T → Msg) : ℝ≥0∞)⁻¹) *
          qprob I H (x tgt) (ρ tgt) (fun p ↦ (out tgt p).2 ≠ tgt (out tgt p).1 ∧
            H (out tgt p) = H ((out tgt p).1, tgt (out tgt p).1)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  mt_spr_uniform_le
    (fun tgt ↦ HybridModel.ofProgram I (x tgt) (ρ tgt) q (hx tgt) (out tgt)) (fun _ ↦ id)

/-- **Second-preimage resistance of a random function, fixed target, for quantum query
programs.**  For every fixed `tgt : X` and every program `x` with at most `q` oracle calls on
every path: `H ← (X → Y)` uniform; the program wins iff its decoded output `x'` satisfies
`x' ≠ tgt` and `H x' = H tgt`.  Bound `(2q+1)² / |Y|`. -/
theorem spr_fixed_program_le {X : Type} [Fintype X] [DecidableEq X] (tgt : X) (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (q : ℕ)
    (hx : QueryBounded x q) (out : (Σ u, W u) → X) :
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        qprob I H x ρ (fun p ↦ out p ≠ tgt ∧ H (out p) = H tgt) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  spr_fixed_le tgt (HybridModel.ofProgram I x ρ q hx out) id

/-- **Second-preimage resistance of a random function, uniform target, for quantum query
programs.**  `H ← (X → Y)` uniform, `tgt ← X` uniform; the program `x tgt` (at most `q` oracle
calls on every path) wins iff its decoded output `x'` satisfies `x' ≠ tgt` and `H x' = H tgt`.
Bound `(2q+1)² / |Y|`. -/
theorem spr_uniform_program_le {X : Type} [Fintype X] [DecidableEq X] (I : L.Interp)
    (x : X → QuantumComp L (qromSpec X Y) W A) (ρ : X → SubState A) (q : ℕ)
    (hx : ∀ tgt, QueryBounded (x tgt) q) (out : X → (Σ u, W u) → X) :
    ∑ H : X → Y, ∑ tgt : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          qprob I H (x tgt) (ρ tgt) (fun p ↦ out tgt p ≠ tgt ∧ H (out tgt p) = H tgt) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  spr_uniform_le
    (fun tgt ↦ HybridModel.ofProgram I (x tgt) (ρ tgt) q (hx tgt) (out tgt)) (fun _ ↦ id)

end Programs

end PQ.QROM

#print axioms PQ.QROM.sum_marked_view
#print axioms PQ.QROM.search_engine
#print axioms PQ.QROM.mt_preimage_uniform_le
#print axioms PQ.QROM.mt_preimage_planted_le
#print axioms PQ.QROM.mt_spr_fixed_le
#print axioms PQ.QROM.mt_spr_uniform_le
#print axioms PQ.QROM.mt_preimage_uniform_program_le
#print axioms PQ.QROM.mt_preimage_planted_program_le
#print axioms PQ.QROM.mt_spr_fixed_program_le
#print axioms PQ.QROM.mt_spr_uniform_program_le
#print axioms PQ.QROM.spr_fixed_le
#print axioms PQ.QROM.spr_uniform_le
#print axioms PQ.QROM.spr_fixed_program_le
#print axioms PQ.QROM.spr_uniform_program_le
