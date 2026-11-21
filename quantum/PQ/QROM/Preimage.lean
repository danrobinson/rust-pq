import PQ.QROM.Average
import PQ.QROM.Product

/-!
# Preimage resistance of a random function against quantum queries

`preimage_uniform_le`: for a uniformly random `H : X → Y` and an independent uniform target `y`,
every `q`-query algorithm outputs a preimage of `y` with probability at most `(2q+1)² / |Y|`.

Proof: hidden-set lemma (`Hidden.search_le`) for the coupling in which every marked point
(`H k = y`) is resampled to a uniform value different from `y`.  The view `(y, G)` (`G` the
resampled function) is independent of which points were marked: given the view, each point is
marked with probability exactly `1/|Y|` (`hidden_uniform`, from the product change of variables
`sum_comp_coord_change`).
-/

open ENNReal Finset

namespace PQ.QROM

/-- Nonzero elements: the resampling offsets. -/
abbrev NZ (Y : Type) [Zero Y] : Type := {d : Y // d ≠ 0}

theorem natCast_mul_inv_cancel {n : ℕ} (hn : n ≠ 0) : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by simpa using hn) (ENNReal.natCast_ne_top n)

section

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The hybrid value at a point with real value `t.1` and offset `t.2`: a value equal to the
target `y` is moved to `y + t.2 ≠ y`. -/
def resample (y : Y) (t : Y × NZ Y) : Y := if t.1 = y then y + t.2 else t.1

omit [Fintype Y] in
theorem resample_ne (y : Y) (t : Y × NZ Y) : resample y t ≠ y := by
  unfold resample
  split_ifs with h
  · simpa using t.2.2
  · exact h

theorem card_NZ_add_one : Fintype.card (NZ Y) + 1 = Fintype.card Y := by
  have h := Fintype.card_subtype_compl (fun d : Y ↦ d = 0)
  have h1 : Fintype.card {d : Y // d = 0} = 1 := Fintype.card_subtype_eq 0
  have hpos : 0 < Fintype.card Y := Fintype.card_pos
  rw [h1] at h
  have : Fintype.card (NZ Y) = Fintype.card Y - 1 := h
  omega

theorem sum_NZ_ite (y z : Y) (hz : z ≠ y) (v : ℝ≥0∞) :
    ∑ d : NZ Y, (if y + (d : Y) = z then v else 0) = v := by
  rw [Finset.sum_eq_single (⟨z - y, sub_ne_zero.2 hz⟩ : NZ Y)]
  · simp
  · intro d _ hd
    refine ite_eq_right_iff.2 fun h ↦ ?_
    exact absurd (Subtype.ext (by simp [← h])) hd
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The marking indicator and the constant `1/|Y|` have the same push-forward under
`resample y`: given the hybrid value, a point is marked with probability `1/|Y|`. -/
theorem resample_fiber (y z : Y) :
    ∑ t : Y × NZ Y with resample y t = z, (if t.1 = y then (1 : ℝ≥0∞) else 0) =
      ∑ t : Y × NZ Y with resample y t = z, (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  by_cases hz : z = y
  · have : (univ.filter fun t : Y × NZ Y ↦ resample y t = z) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun t _ h ↦ resample_ne y t (h.trans hz)
    rw [this]; simp
  · rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hL : ∑ h : Y, ∑ d : NZ Y,
        (if resample y (h, d) = z then (if (h, d).1 = y then (1 : ℝ≥0∞) else 0) else 0) = 1 := by
      rw [Finset.sum_eq_single y]
      · simpa [resample] using sum_NZ_ite y z hz 1
      · intro h _ hh
        simp [hh]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : ∑ h : Y, ∑ d : NZ Y,
        (if resample y (h, d) = z then (Fintype.card Y : ℝ≥0∞)⁻¹ else 0) = 1 := by
      rw [Fintype.sum_eq_add y z (Ne.symm hz)]
      · have h1 : ∑ d : NZ Y, (if resample y (y, d) = z then (Fintype.card Y : ℝ≥0∞)⁻¹ else 0) =
            (Fintype.card Y : ℝ≥0∞)⁻¹ := by
          simpa [resample] using sum_NZ_ite y z hz (Fintype.card Y : ℝ≥0∞)⁻¹
        have h2 : ∑ d : NZ Y, (if resample y (z, d) = z then (Fintype.card Y : ℝ≥0∞)⁻¹ else 0) =
            Fintype.card (NZ Y) * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
          simp [resample, hz]
        rw [h1, h2]
        calc (Fintype.card Y : ℝ≥0∞)⁻¹ + Fintype.card (NZ Y) * (Fintype.card Y : ℝ≥0∞)⁻¹
            = ((Fintype.card (NZ Y) + 1 : ℕ) : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
              push_cast; ring
          _ = 1 := by
              rw [card_NZ_add_one]
              exact natCast_mul_inv_cancel Fintype.card_ne_zero
      · intro h hh
        refine Finset.sum_eq_zero fun d _ ↦ ?_
        simp [resample, hh.1, hh.2]
    rw [hL, hR]

variable {X : Type} [Fintype X] [DecidableEq X]

/-- In the resampling coupling for a uniform target, the marked set `{k | H k = y}` is
`1/|Y|`-hidden from the view `(y, G)`. -/
theorem hidden_uniform (κ : ℝ≥0∞) :
    Hidden (Ω := Y × (X → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ (ω.1, fun k ↦ resample ω.1 (ω.2 k)))
      (fun ω ↦ univ.filter fun k ↦ (ω.2 k).1 = ω.1) (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  refine le_of_eq ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have e3 := sum_comp_coord_change k (resample y) (fun t ↦ if t.1 = y then (1 : ℝ≥0∞) else 0)
    (fun _ ↦ (Fintype.card Y : ℝ≥0∞)⁻¹) (resample_fiber y) (fun G ↦ φ (y, G))
  simp only [Function.comp_def] at e3
  calc ∑ τ : X → Y × NZ Y, κ * (if (τ k).1 = y then φ (y, fun k ↦ resample y (τ k)) else 0)
      = κ * ∑ τ : X → Y × NZ Y,
          (if (τ k).1 = y then (1 : ℝ≥0∞) else 0) * φ (y, fun k ↦ resample y (τ k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ ↦ ?_
        split_ifs <;> simp
    _ = κ * ∑ τ : X → Y × NZ Y,
          (Fintype.card Y : ℝ≥0∞)⁻¹ * φ (y, fun k ↦ resample y (τ k)) := by rw [e3]
    _ = (Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ τ : X → Y × NZ Y, κ * φ (y, fun k ↦ resample y (τ k)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, mul_left_comm]

variable {Leaf : Type} {q : ℕ}

omit [Fintype Y] [AddCommGroup Y] [DecidableEq X] in
/-- Any event of the form "the output lies in a set" has probability at most one, given
subadditivity of the output distribution. -/
theorem prob_le_one_of_sub (M : HybridModel X Y Leaf q) (out : Leaf → X)
    (hsub : ∀ (H : X → Y) (T : Finset X),
      M.prob H (fun p ↦ out p ∈ T) ≤ ∑ k ∈ T, M.prob H (fun p ↦ out p = k))
    (H : X → Y) (E : Leaf → Prop) : M.prob H E ≤ 1 :=
  calc M.prob H E ≤ M.prob H (fun p ↦ out p ∈ (univ : Finset X)) :=
        M.prob_mono H fun _ _ ↦ Finset.mem_univ _
    _ ≤ ∑ k, M.prob H (fun p ↦ out p = k) := hsub H univ
    _ ≤ 1 := M.prob_sum_le H out

theorem one_le_two_mul_add_one_sq (q : ℕ) : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 :=
  one_le_pow₀ le_add_self

/-- **Preimage resistance of a random function, uniform target.**  Experiment: `H ← (X → Y)`
uniform, `y ← Y` uniform, the `q`-query algorithm `M y` runs with quantum access to `H` and
outputs `out y p`; it wins iff `H (out y p) = y`.  The winning probability is at most
`(2q+1)² / |Y|`. -/
theorem preimage_uniform_le (M : Y → HybridModel X Y Leaf q) (out : Y → Leaf → X) :
    ∑ H : X → Y, ∑ y : Y,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card Y : ℝ≥0∞)⁻¹) *
          (M y).prob H (fun p ↦ H (out y p) = y) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  have hXY : Fintype.card (X → Y) ≠ 0 := Fintype.card_ne_zero
  have hY : Fintype.card Y ≠ 0 := Fintype.card_ne_zero
  by_cases hN : Fintype.card Y = 1
  · -- trivial case: the bound is at least one
    rw [hN, Nat.cast_one, div_one]
    refine le_trans ?_ (one_le_two_mul_add_one_sq q)
    calc ∑ H : X → Y, ∑ y : Y, ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * ((1 : ℕ) : ℝ≥0∞)⁻¹) *
            (M y).prob H (fun p ↦ H (out y p) = y)
        ≤ ∑ _H : X → Y, ∑ _y : Y, ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * ((1 : ℕ) : ℝ≥0∞)⁻¹) * 1 := by
          gcongr with H _ y _
          exact prob_le_one_of_sub (M y) (out y) (fun H T ↦ (M y).prob_sub H (out y) T) H _
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, hN, nsmul_eq_mul, Nat.cast_one, inv_one,
            mul_one, one_mul]
          exact natCast_mul_inv_cancel hXY
  · have hnt : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
    have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
    have hXD : Fintype.card (X → NZ Y) ≠ 0 := Fintype.card_ne_zero
    set cN : ℝ≥0∞ := (Fintype.card Y : ℝ≥0∞) with hcN
    set cXY : ℝ≥0∞ := (Fintype.card (X → Y) : ℝ≥0∞) with hcXY
    set cXD : ℝ≥0∞ := (Fintype.card (X → NZ Y) : ℝ≥0∞) with hcXD
    have iN : cN * cN⁻¹ = 1 := natCast_mul_inv_cancel hY
    have iXY : cXY * cXY⁻¹ = 1 := natCast_mul_inv_cancel hXY
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
    set κ : ℝ≥0∞ := cN⁻¹ * cXY⁻¹ * cXD⁻¹ with hκ
    have hw : ∑ _ω : Y × (X → Y × NZ Y), κ ≤ 1 := by
      refine le_of_eq ?_
      rw [Fintype.sum_prod_type]
      have := sum_fst_comp (X := X) (A := Y) (B := NZ Y) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cN * (cXD * (cXY * κ)) = (cN * cN⁻¹) * (cXY * cXY⁻¹) * (cXD * cXD⁻¹) := by
            rw [hκ]; ring
        _ = 1 := by rw [iN, iXY, iXD]; simp
    have hs := (hidden_uniform (X := X) (Y := Y) κ).search_le hw (fun v ↦ M v.1)
      (fun ω k ↦ (ω.2 k).1) (fun v ↦ v.2)
      (by
        intro ω k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hne
        exact hk (by simp [resample, hne]))
      (fun v ↦ out v.1)
    rw [div_eq_mul_inv]
    refine le_trans (le_of_eq ?_) hs
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have ev : ∀ τ : X → Y × NZ Y,
        (fun p ↦ out y p ∈ univ.filter fun k ↦ (τ k).1 = y) = fun p ↦ (τ (out y p)).1 = y := by
      intro τ; funext p; simp
    have e := sum_fst_comp (X := X) (A := Y) (B := NZ Y)
      (fun H ↦ κ * (M y).prob H (fun p ↦ H (out y p) = y))
    simp only [ev]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    calc cXY⁻¹ * cN⁻¹ * (M y).prob H (fun p ↦ H (out y p) = y)
        = (cXD * cXD⁻¹) * (cXY⁻¹ * cN⁻¹ * (M y).prob H (fun p ↦ H (out y p) = y)) := by
          rw [iXD, one_mul]
      _ = cXD * (κ * (M y).prob H (fun p ↦ H (out y p) = y)) := by rw [hκ]; ring


/-! ### Planted target -/

/-- Given the hybrid function, a point is marked with probability `1/|Y|` (fixed target). -/
theorem sum_marked_eq (y : Y) (k : X) (Φ : (X → Y) → ℝ≥0∞) :
    ∑ τ : X → Y × NZ Y,
        (if (τ k).1 = y then (1 : ℝ≥0∞) else 0) * Φ (fun j ↦ resample y (τ j)) =
      (Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ τ : X → Y × NZ Y, Φ (fun j ↦ resample y (τ j)) := by
  have e3 := sum_comp_coord_change k (resample y) (fun t ↦ if t.1 = y then (1 : ℝ≥0∞) else 0)
    (fun _ ↦ (Fintype.card Y : ℝ≥0∞)⁻¹) (resample_fiber y) Φ
  simp only [Function.comp_def] at e3
  rw [e3, Finset.mul_sum]

/-- Two distinct points are marked independently given the hybrid function. -/
theorem sum_marked_marked_eq (y : Y) (x k : X) (hxk : x ≠ k) (Φ : (X → Y) → ℝ≥0∞) :
    ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
        ((if (τ k).1 = y then (1 : ℝ≥0∞) else 0) * Φ (fun j ↦ resample y (τ j))) =
      (Fintype.card Y : ℝ≥0∞)⁻¹ *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ τ : X → Y × NZ Y, Φ (fun j ↦ resample y (τ j))) := by
  have e := sum_coord_change k (resample y) (resample y)
    (fun t ↦ if t.1 = y then (1 : ℝ≥0∞) else 0)
    (fun _ ↦ (Fintype.card Y : ℝ≥0∞)⁻¹) (resample_fiber y)
    (fun z τ ↦ (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
      Φ (Function.update (fun j ↦ resample y (τ j)) k z))
    (by
      intro z τ t
      have h1 : Function.update τ k t x = τ x := Function.update_of_ne hxk _ _
      have h2 : Function.update (fun j ↦ resample y (Function.update τ k t j)) k z =
          Function.update (fun j ↦ resample y (τ j)) k z := by
        funext j
        by_cases hj : j = k
        · subst hj; simp
        · simp [Function.update, hj]
      rw [h1, h2])
  have hupd : ∀ τ : X → Y × NZ Y,
      Function.update (fun j ↦ resample y (τ j)) k (resample y (τ k)) =
        fun j ↦ resample y (τ j) := fun τ ↦
    Function.update_eq_self k fun j ↦ resample y (τ j)
  simp only [hupd] at e
  calc ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) *
        ((if (τ k).1 = y then (1 : ℝ≥0∞) else 0) * Φ (fun j ↦ resample y (τ j)))
      = ∑ τ : X → Y × NZ Y, (if (τ k).1 = y then (1 : ℝ≥0∞) else 0) *
        ((if (τ x).1 = y then (1 : ℝ≥0∞) else 0) * Φ (fun j ↦ resample y (τ j))) :=
        Finset.sum_congr rfl fun τ _ ↦ mul_left_comm _ _ _
    _ = ∑ τ : X → Y × NZ Y, (Fintype.card Y : ℝ≥0∞)⁻¹ *
        ((if (τ x).1 = y then (1 : ℝ≥0∞) else 0) * Φ (fun j ↦ resample y (τ j))) := e
    _ = _ := by rw [← Finset.mul_sum, sum_marked_eq]

/-- Splitting a sum according to the value at the coordinate `x`. -/
theorem sum_split_value (x : X) (g : Y → (X → Y × NZ Y) → ℝ≥0∞) :
    ∑ τ : X → Y × NZ Y, g (τ x).1 τ =
      ∑ y : Y, ∑ τ : X → Y × NZ Y, (if (τ x).1 = y then (1 : ℝ≥0∞) else 0) * g y τ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  simp [ite_mul]

/-- In the resampling coupling for a planted target `y = H x*`, the marked set `{k | H k = y}`
is `(1/|Y| + 1/|X|)`-hidden from the view `(y, G)`: given the view, `k` is the planted point with
probability `1/|X|` and is otherwise marked with probability `1/|Y|`. -/
theorem hidden_planted (κ : ℝ≥0∞) :
    Hidden (Ω := X × (X → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ ((ω.2 ω.1).1, fun k ↦ resample (ω.2 ω.1).1 (ω.2 k)))
      (fun ω ↦ univ.filter fun k ↦ (ω.2 k).1 = (ω.2 ω.1).1)
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card X : ℝ≥0∞)⁻¹) := by
  intro k φ
  set cN : ℝ≥0∞ := (Fintype.card Y : ℝ≥0∞) with hcN
  set cX : ℝ≥0∞ := (Fintype.card X : ℝ≥0∞) with hcX
  have iX : cX⁻¹ * cX = 1 := by
    have : Nonempty X := ⟨k⟩
    rw [mul_comm]
    exact natCast_mul_inv_cancel Fintype.card_ne_zero
  set B : ℝ≥0∞ := ∑ y : Y, ∑ τ : X → Y × NZ Y, φ (y, fun j ↦ resample y (τ j)) with hB
  have hA : ∀ x : X, ∑ τ : X → Y × NZ Y, φ ((τ x).1, fun j ↦ resample (τ x).1 (τ j)) =
      cN⁻¹ * B := by
    intro x
    rw [sum_split_value x fun y τ ↦ φ (y, fun j ↦ resample y (τ j)), hB, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ ↦ sum_marked_eq y x fun G ↦ φ (y, G)
  have hT : ∀ x : X, ∑ τ : X → Y × NZ Y,
      (if (τ k).1 = (τ x).1 then φ ((τ x).1, fun j ↦ resample (τ x).1 (τ j)) else 0) ≤
        (if x = k then cN⁻¹ * B else 0) + cN⁻¹ * (cN⁻¹ * B) := by
    intro x
    by_cases hx : x = k
    · subst hx
      simp only [ite_true]
      rw [hA]
      exact le_self_add
    · simp only [hx, ↓reduceIte, zero_add]
      rw [sum_split_value x fun y τ ↦
          if (τ k).1 = y then φ (y, fun j ↦ resample y (τ j)) else 0,
        hB, Finset.mul_sum, Finset.mul_sum]
      refine le_of_eq (Finset.sum_congr rfl fun y _ ↦ ?_)
      rw [← sum_marked_marked_eq y x k hx fun G ↦ φ (y, G)]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      split_ifs <;> simp
  have hL : ∑ ω : X × (X → Y × NZ Y), κ * (if k ∈ univ.filter (fun j ↦ (ω.2 j).1 = (ω.2 ω.1).1)
      then φ ((ω.2 ω.1).1, fun j ↦ resample (ω.2 ω.1).1 (ω.2 j)) else 0) =
      κ * ∑ x : X, ∑ τ : X → Y × NZ Y,
        (if (τ k).1 = (τ x).1 then φ ((τ x).1, fun j ↦ resample (τ x).1 (τ j)) else 0) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mul_sum]
  have hR : ∑ ω : X × (X → Y × NZ Y),
      κ * φ ((ω.2 ω.1).1, fun j ↦ resample (ω.2 ω.1).1 (ω.2 j)) = κ * (cX * (cN⁻¹ * B)) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hA, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcX]
    ring
  rw [hL, hR]
  calc κ * ∑ x : X, ∑ τ : X → Y × NZ Y,
        (if (τ k).1 = (τ x).1 then φ ((τ x).1, fun j ↦ resample (τ x).1 (τ j)) else 0)
      ≤ κ * ∑ x : X, ((if x = k then cN⁻¹ * B else 0) + cN⁻¹ * (cN⁻¹ * B)) := by
        gcongr with x _
        exact hT x
    _ = κ * (cN⁻¹ * B + cX * (cN⁻¹ * (cN⁻¹ * B))) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, hcX]
    _ = κ * (cX⁻¹ * cX * (cN⁻¹ * B) + cX * (cN⁻¹ * (cN⁻¹ * B))) := by rw [iX, one_mul]
    _ = (cN⁻¹ + cX⁻¹) * (κ * (cX * (cN⁻¹ * B))) := by ring

/-- **Preimage resistance of a random function, planted target.**  Experiment: `H ← (X → Y)`
uniform, `x* ← X` uniform, `y := H x*`; the `q`-query algorithm `M y` runs with quantum access to
`H` and outputs `out y p`; it wins iff `H (out y p) = y`.  The winning probability is at most
`(2q+1)² (1/|Y| + 1/|X|)`. -/
theorem preimage_planted_le (M : Y → HybridModel X Y Leaf q) (out : Y → Leaf → X) :
    ∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          (M (H x)).prob H (fun p ↦ H (out (H x) p) = H x) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card X : ℝ≥0∞)⁻¹) := by
  have hXY : Fintype.card (X → Y) ≠ 0 := Fintype.card_ne_zero
  set cN : ℝ≥0∞ := (Fintype.card Y : ℝ≥0∞) with hcN
  set cX : ℝ≥0∞ := (Fintype.card X : ℝ≥0∞) with hcX
  set cXY : ℝ≥0∞ := (Fintype.card (X → Y) : ℝ≥0∞) with hcXY
  have iXY : cXY * cXY⁻¹ = 1 := natCast_mul_inv_cancel hXY
  have iX : cX * cX⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
    · simp [hcX, h]
    · exact le_of_eq (natCast_mul_inv_cancel h.ne')
  by_cases hN : Fintype.card Y = 1
  · -- trivial case: the bound is at least one
    have h1 : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 * (cN⁻¹ + cX⁻¹) := by
      have : cN⁻¹ = 1 := by simp [hcN, hN]
      calc (1 : ℝ≥0∞) = 1 * 1 := (mul_one 1).symm
        _ ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 * (cN⁻¹ + cX⁻¹) :=
            mul_le_mul' (one_le_two_mul_add_one_sq q) (this ▸ le_self_add)
    refine le_trans ?_ h1
    calc ∑ H : X → Y, ∑ x : X, (cXY⁻¹ * cX⁻¹) *
            (M (H x)).prob H (fun p ↦ H (out (H x) p) = H x)
        ≤ ∑ _H : X → Y, ∑ _x : X, (cXY⁻¹ * cX⁻¹) * 1 := by
          gcongr with H _ x _
          exact prob_le_one_of_sub (M (H x)) (out (H x)) (fun H' T ↦ (M (H x)).prob_sub H' (out (H x)) T) H _
      _ = (cXY * cXY⁻¹) * (cX * cX⁻¹) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcX, hcXY]
          ring
      _ ≤ 1 := by rw [iXY, one_mul]; exact iX
  · have hnt : Nontrivial Y :=
      Fintype.one_lt_card_iff_nontrivial.1
        (by have := Fintype.card_pos (α := Y); omega)
    obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
    have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
    have hXD : Fintype.card (X → NZ Y) ≠ 0 := Fintype.card_ne_zero
    set cXD : ℝ≥0∞ := (Fintype.card (X → NZ Y) : ℝ≥0∞) with hcXD
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
    set κ : ℝ≥0∞ := cX⁻¹ * cXY⁻¹ * cXD⁻¹ with hκ
    have hw : ∑ _ω : X × (X → Y × NZ Y), κ ≤ 1 := by
      rw [Fintype.sum_prod_type]
      have := sum_fst_comp (X := X) (A := Y) (B := NZ Y) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cX * (cXD * (cXY * κ)) = (cX * cX⁻¹) * ((cXY * cXY⁻¹) * (cXD * cXD⁻¹)) := by
            rw [hκ]; ring
        _ ≤ 1 := by rw [iXY, iXD, mul_one, mul_one]; exact iX
    have hs := (hidden_planted (X := X) (Y := Y) κ).search_le hw (fun v ↦ M v.1)
      (fun ω k ↦ (ω.2 k).1) (fun v ↦ v.2)
      (by
        intro ω k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hne
        exact hk (by simp [resample, hne]))
      (fun v ↦ out v.1)
    refine le_trans (le_of_eq ?_) hs
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have ev : ∀ τ : X → Y × NZ Y,
        (fun p ↦ out (τ x).1 p ∈ univ.filter fun k ↦ (τ k).1 = (τ x).1) =
          fun p ↦ (τ (out (τ x).1 p)).1 = (τ x).1 := by
      intro τ; funext p; simp
    have e := sum_fst_comp (X := X) (A := Y) (B := NZ Y)
      (fun H ↦ κ * (M (H x)).prob H (fun p ↦ H (out (H x) p) = H x))
    simp only [ev]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    calc cXY⁻¹ * cX⁻¹ * (M (H x)).prob H (fun p ↦ H (out (H x) p) = H x)
        = (cXD * cXD⁻¹) * (cXY⁻¹ * cX⁻¹ * (M (H x)).prob H (fun p ↦ H (out (H x) p) = H x)) := by
          rw [iXD, one_mul]
      _ = cXD * (κ * (M (H x)).prob H (fun p ↦ H (out (H x) p) = H x)) := by rw [hκ]; ring

end

end PQ.QROM

#print axioms PQ.QROM.preimage_uniform_le
#print axioms PQ.QROM.preimage_planted_le
