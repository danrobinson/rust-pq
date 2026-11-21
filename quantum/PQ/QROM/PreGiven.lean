import PQ.QROM.SprGiven

/-!
# Planted-target multi-target PRE on an embedded random row, with observations and weights

Same embedded-row setting as `spr_embedded_obs_weighted_le`: the oracle is `patch F e R` (`F`
fixed, `R : Tw × Msg → Y` uniform on the range of `e : Tw × Msg ↪ Z`).  A hidden input
`xs t : Msg` is planted for every tweak (`xs` uniform), and `c : Tw → Bool` is the set of requested
tweaks.  The adversary's program, its decoding and a weight depend on an observation
`o (tvals c R xs) R xs`, where `tvals c R xs t = some (R (t, xs t))` for requested `t`, and `o`
depends on `R`, `xs` otherwise only through the rows of the tweaks that were NOT requested
(hypotheses `h1`, `h2`).  The adversary outputs `(t, x')` and wins iff `t` was requested and
`R (t, x') = R (t, xs t)`.

`pre_embedded_obs_weighted_le`: the weighted winning probability is at most
`(2q+1)² (1/|Y| + 1/|Msg|)` times the average weight.

Coupling: that of `mt_preimage_planted_le` on the requested rows (every point of a requested row
whose value equals the target value, the planted point included, is resampled away from it); the
other rows are untouched.  Given the view, a point of a requested row is the planted point with
probability `1/|Msg|` and is otherwise marked with probability `1/|Y|` (`hidden_pg`).
-/

open ENNReal Finset

namespace PQ.QROM

/-- From a bound for normalised weights to a bound proportional to the average weight. -/
theorem le_mul_sum_of_normalised {Ωs : Type} [Fintype Ωs] (cw B : ℝ≥0∞) (hc0 : cw ≠ 0)
    (hB : B ≠ 0) (wt p : Ωs → ℝ≥0∞)
    (hn : ∀ s : ℝ≥0∞, ∑ r, cw * (wt r * s) ≤ 1 → ∑ r, cw * (wt r * s * p r) ≤ B) :
    ∑ r, cw * (wt r * p r) ≤ B * ∑ r, cw * wt r := by
  set Wt : ℝ≥0∞ := ∑ r, cw * wt r with hWt
  by_cases h0 : Wt = 0
  · have hz : ∀ r, wt r = 0 := by
      intro r
      have := (Finset.sum_eq_zero_iff.1 h0) r (Finset.mem_univ r)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc0
      · exact h
    simp [hz]
  by_cases htop : Wt = ⊤
  · rw [htop, ENNReal.mul_top hB]
    exact le_top
  · have iW : Wt⁻¹ * Wt = 1 := ENNReal.inv_mul_cancel h0 htop
    have h := hn Wt⁻¹ (le_of_eq (by
      calc ∑ r, cw * (wt r * Wt⁻¹) = Wt⁻¹ * Wt := by
            rw [hWt, Finset.mul_sum]
            exact Finset.sum_congr rfl fun r _ ↦ by ring
        _ = 1 := iW))
    calc ∑ r, cw * (wt r * p r) = (∑ r, cw * (wt r * Wt⁻¹ * p r)) * Wt := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          calc cw * (wt r * p r) = cw * (wt r * p r) * (Wt⁻¹ * Wt) := by rw [iW, mul_one]
            _ = _ := by ring
      _ ≤ B * Wt := mul_le_mul' h le_rfl

section

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]

/-- The target values handed to the adversary: `R (t, xs t)` for every requested tweak. -/
def tvals (c : Tw → Bool) (R : Tw × Msg → Y) (xs : Tw → Msg) : Tw → Option Y :=
  fun t ↦ if c t = true then some (R (t, xs t)) else none

/-- The marked set: the points of requested rows whose value is the target value. -/
def pgMarked (c : Tw → Bool) (xs : Tw → Msg) (R : Tw × Msg → Y) : Finset (Tw × Msg) :=
  univ.filter fun k ↦ c k.1 = true ∧ R k = R (k.1, xs k.1)

variable [AddCommGroup Y]

/-- The hybrid function: on requested rows every point is resampled away from the target value;
other rows are kept. -/
def pgG (c : Tw → Bool) (xs : Tw → Msg) (τ : Tw × Msg → Y × NZ Y) (j : Tw × Msg) : Y :=
  if c j.1 = true then resample (τ (j.1, xs j.1)).1 (τ j) else (τ j).1

/-- Given the view (observation and hybrid function), a point is marked with probability at most
`1/|Y| + 1/|Msg|`. -/
theorem hidden_pg {A : Type} (c : Tw → Bool)
    (o : (Tw → Option Y) → (Tw × Msg → Y) → (Tw → Msg) → A)
    (h1 : ∀ k : Tw × Msg, c k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y)
      (xs : Tw → Msg) (v : Y), o yv (Function.update R k v) xs = o yv R xs)
    (h2 : ∀ t : Tw, c t = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y)
      (xs : Tw → Msg) (m : Msg), o yv R (Function.update xs t m) = o yv R xs)
    (κ : ℝ≥0∞) :
    Hidden (Ω := (Tw → Msg) × (Tw × Msg → Y × NZ Y)) (fun _ ↦ κ)
      (fun ω ↦ (o (tvals c (fun k ↦ (ω.2 k).1) ω.1) (fun k ↦ (ω.2 k).1) ω.1, pgG c ω.1 ω.2))
      (fun ω ↦ pgMarked c ω.1 (fun k ↦ (ω.2 k).1))
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  intro k φ
  obtain ⟨t, x⟩ := k
  by_cases hct : c t = true
  swap
  · simp [pgMarked, hct]
  set cN : ℝ≥0∞ := (Fintype.card Y : ℝ≥0∞) with hcN
  set cM : ℝ≥0∞ := (Fintype.card Msg : ℝ≥0∞) with hcM
  have hfstupd : ∀ (τ : Tw × Msg → Y × NZ Y) (k : Tw × Msg) (v : Y × NZ Y),
      (fun j ↦ (Function.update τ k v j).1) = Function.update (fun j ↦ (τ j).1) k v.1 := by
    intro τ k v
    funext j
    by_cases hj : j = k
    · rw [hj]; simp
    · simp [Function.update_of_ne hj]
  let V : (Tw → Msg) → (Tw × Msg → Y × NZ Y) → A × (Tw × Msg → Y) := fun xs τ ↦
    (o (tvals c (fun j ↦ (τ j).1) xs) (fun j ↦ (τ j).1) xs, pgG c xs τ)
  let yv : Y → (Tw → Msg) → (Tw × Msg → Y × NZ Y) → Tw → Option Y := fun y xs τ t' ↦
    if t' = t then some y else tvals c (fun j ↦ (τ j).1) xs t'
  let gy : Y → (Tw → Msg) → (Tw × Msg → Y × NZ Y) → Tw × Msg → Y := fun y xs τ j ↦
    if j.1 = t then resample y (τ j) else pgG c xs τ j
  let V' : Y → (Tw → Msg) → (Tw × Msg → Y × NZ Y) → A × (Tw × Msg → Y) := fun y xs τ ↦
    (o (yv y xs τ) (fun j ↦ (τ j).1) xs, gy y xs τ)
  let Aw : (Tw → Msg) → ℝ≥0∞ := fun xs ↦ ∑ τ : Tw × Msg → Y × NZ Y, φ (V xs τ)
  let Bw : (Tw → Msg) → ℝ≥0∞ := fun xs ↦ ∑ y : Y, ∑ τ : Tw × Msg → Y × NZ Y, φ (V' y xs τ)
  have hV : ∀ xs τ, V' (τ (t, xs t)).1 xs τ = V xs τ := by
    intro xs τ
    have e1 : yv (τ (t, xs t)).1 xs τ = tvals c (fun j ↦ (τ j).1) xs := by
      funext t'
      by_cases h : t' = t
      · subst h; simp [yv, tvals, hct]
      · simp [yv, h]
    have e2 : gy (τ (t, xs t)).1 xs τ = pgG c xs τ := by
      funext j
      by_cases h : j.1 = t
      · simp [gy, pgG, h, hct]
      · simp [gy, h]
    simp only [V, V', e1, e2]
  have hA : ∀ xs, Aw xs = cN⁻¹ * Bw xs := by
    intro xs
    have h1' : Aw xs = ∑ τ : Tw × Msg → Y × NZ Y, φ (V' (τ (t, xs t)).1 xs τ) :=
      Finset.sum_congr rfl fun τ _ ↦ by rw [hV]
    rw [h1', sum_split_value (t, xs t) fun y τ ↦ φ (V' y xs τ)]
    show _ = cN⁻¹ * ∑ y : Y, ∑ τ : Tw × Msg → Y × NZ Y, φ (V' y xs τ)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hyvupd : ∀ (τ : Tw × Msg → Y × NZ Y) (v : Y × NZ Y),
        yv y xs (Function.update τ (t, xs t) v) = yv y xs τ := by
      intro τ v
      funext t'
      by_cases h : t' = t
      · simp [yv, h]
      · have : (t', xs t') ≠ (t, xs t) := fun h' ↦ h (congrArg Prod.fst h')
        simp [yv, h, tvals]
    exact sum_marked_view (X := Tw × Msg) (t, xs t) (fun _ ↦ y) (fun _ _ ↦ rfl)
      (gy y xs) (fun τ ↦ by simp [gy])
      (fun τ v j hj ↦ by
        by_cases h : j.1 = t
        · simp [gy, h, Function.update_of_ne hj]
        · have : (j.1, xs j.1) ≠ (t, xs t) := fun h' ↦ h (congrArg Prod.fst h')
          simp [gy, pgG, h, Function.update_of_ne hj])
      (fun τ g ↦ φ (o (yv y xs τ) (fun j ↦ (τ j).1) xs, g))
      (fun τ v g ↦ by rw [hyvupd, hfstupd, h1 (t, xs t) hct])
  have hBinv : ∀ (z : Unit) (xs : Tw → Msg) (m : Msg),
      (fun (_ : Unit) xs ↦ Bw xs) z (Function.update xs t m) =
        (fun (_ : Unit) xs ↦ Bw xs) z xs := by
    intro _ xs m
    have e1 : ∀ y τ, yv y (Function.update xs t m) τ = yv y xs τ := by
      intro y τ
      funext t'
      by_cases h : t' = t
      · simp [yv, h]
      · simp [yv, h, tvals]
    have e2 : ∀ y τ, gy y (Function.update xs t m) τ = gy y xs τ := by
      intro y τ
      funext j
      by_cases h : j.1 = t
      · simp [gy, h]
      · simp [gy, pgG, h]
    simp only [Bw, V', e1, e2, h2 t hct]
  have hplant : ∑ xs : Tw → Msg, (if xs t = x then Aw xs else 0) =
      cM⁻¹ * ∑ xs : Tw → Msg, Aw xs := by
    have e := sum_coord_change t (fun _ : Msg ↦ ()) (fun _ : Msg ↦ ())
      (fun m ↦ if m = x then (1 : ℝ≥0∞) else 0) (fun _ ↦ cM⁻¹)
      (by
        intro z
        have : Nonempty Msg := ⟨x⟩
        simp only [Finset.filter_true_of_mem, Finset.mem_univ, implies_true, Finset.sum_ite_eq',
          ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact (natCast_mul_inv_cancel Fintype.card_ne_zero).symm)
      (fun _ xs ↦ Bw xs) hBinv
    calc ∑ xs : Tw → Msg, (if xs t = x then Aw xs else 0)
        = ∑ xs : Tw → Msg, cN⁻¹ * ((if xs t = x then (1 : ℝ≥0∞) else 0) * Bw xs) := by
          refine Finset.sum_congr rfl fun xs _ ↦ ?_
          rw [hA]
          split_ifs <;> simp
      _ = cN⁻¹ * ∑ xs : Tw → Msg, cM⁻¹ * Bw xs := by rw [← Finset.mul_sum, e]
      _ = cM⁻¹ * ∑ xs : Tw → Msg, Aw xs := by
          simp only [hA, ← Finset.mul_sum]
          ring
  have hT : ∀ xs : Tw → Msg, ∑ τ : Tw × Msg → Y × NZ Y,
      (if (τ (t, x)).1 = (τ (t, xs t)).1 then φ (V xs τ) else 0) ≤
        (if xs t = x then Aw xs else 0) + cN⁻¹ * Aw xs := by
    intro xs
    by_cases hx : xs t = x
    · simp only [hx, ite_true]
      refine le_trans (Finset.sum_le_sum fun τ _ ↦ ?_) le_self_add
      exact le_rfl
    · simp only [hx, ite_false, zero_add]
      have hk' : (t, xs t) ≠ (t, x) := fun h ↦ hx (congrArg Prod.snd h)
      have hj' : ∀ j : Tw × Msg, (j.1, xs j.1) ≠ (t, x) := by
        intro j h
        have e1 : j.1 = t := congrArg Prod.fst h
        have e2 : xs j.1 = x := congrArg Prod.snd h
        exact hx (e1 ▸ e2)
      have htv : ∀ (τ : Tw × Msg → Y × NZ Y) (v : Y × NZ Y),
          tvals c (fun j ↦ (Function.update τ (t, x) v j).1) xs =
            tvals c (fun j ↦ (τ j).1) xs := by
        intro τ v
        funext t'
        simp [tvals, Function.update_of_ne (hj' (t', x))]
      have e := sum_marked_view (X := Tw × Msg) (t, x) (fun τ ↦ (τ (t, xs t)).1)
        (fun τ v ↦ by simp [Function.update_of_ne hk'])
        (pgG c xs) (fun τ ↦ by simp [pgG, hct])
        (fun τ v j hj ↦ by
          simp [pgG, Function.update_of_ne hj, Function.update_of_ne (hj' j)])
        (fun τ g ↦ φ (o (tvals c (fun j ↦ (τ j).1) xs) (fun j ↦ (τ j).1) xs, g))
        (fun τ v g ↦ by rw [htv, hfstupd, h1 (t, x) hct])
      refine le_of_eq ?_
      show _ = cN⁻¹ * ∑ τ : Tw × Msg → Y × NZ Y, φ (V xs τ)
      rw [← e]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      split_ifs <;> simp [V]
  have hL : ∑ ω : (Tw → Msg) × (Tw × Msg → Y × NZ Y),
      κ * (if (t, x) ∈ pgMarked c ω.1 (fun k ↦ (ω.2 k).1)
        then φ (o (tvals c (fun k ↦ (ω.2 k).1) ω.1) (fun k ↦ (ω.2 k).1) ω.1, pgG c ω.1 ω.2)
        else 0) =
      κ * ∑ xs : Tw → Msg, ∑ τ : Tw × Msg → Y × NZ Y,
        (if (τ (t, x)).1 = (τ (t, xs t)).1 then φ (V xs τ) else 0) := by
    rw [Fintype.sum_prod_type]
    simp only [pgMarked, Finset.mem_filter, Finset.mem_univ, true_and, hct, Finset.mul_sum, V]
  have hR : ∑ ω : (Tw → Msg) × (Tw × Msg → Y × NZ Y),
      κ * φ (o (tvals c (fun k ↦ (ω.2 k).1) ω.1) (fun k ↦ (ω.2 k).1) ω.1, pgG c ω.1 ω.2) =
      κ * ∑ xs : Tw → Msg, Aw xs := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, Aw, V]
  rw [hL, hR]
  calc κ * ∑ xs : Tw → Msg, ∑ τ : Tw × Msg → Y × NZ Y,
        (if (τ (t, x)).1 = (τ (t, xs t)).1 then φ (V xs τ) else 0)
      ≤ κ * ∑ xs : Tw → Msg, ((if xs t = x then Aw xs else 0) + cN⁻¹ * Aw xs) := by
        gcongr with xs _
        exact hT xs
    _ = κ * (cM⁻¹ * ∑ xs : Tw → Msg, Aw xs + cN⁻¹ * ∑ xs : Tw → Msg, Aw xs) := by
        rw [Finset.sum_add_distrib, hplant, ← Finset.mul_sum]
    _ = (cN⁻¹ + cM⁻¹) * (κ * ∑ xs : Tw → Msg, Aw xs) := by ring

variable {Leaf : Type} {q : ℕ}

/-- Normalised weighted form: if the weight has average at most one, the weighted winning
probability is at most `(2q+1)² (1/|Y| + 1/|Msg|)`. -/
theorem pre_embedded_obs_normalised_le {A : Type} (e : Tw × Msg ↪ Z) (F : Z → Y)
    (c : Tw → Bool) (o : (Tw → Option Y) → (Tw × Msg → Y) → (Tw → Msg) → A)
    (h1 : ∀ k : Tw × Msg, c k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y)
      (xs : Tw → Msg) (v : Y), o yv (Function.update R k v) xs = o yv R xs)
    (h2 : ∀ t : Tw, c t = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y)
      (xs : Tw → Msg) (m : Msg), o yv R (Function.update xs t m) = o yv R xs)
    (M : A → HybridModel Z Y Leaf q) (out : A → Leaf → Tw × Msg) (w : A → ℝ≥0∞)
    (hw1 : ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
      ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
        w (o (tvals c R xs) R xs) ≤ 1) :
    ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          (w (o (tvals c R xs) R xs) *
            (M (o (tvals c R xs) R xs)).prob (patch F e R)
              (fun l ↦ c (out (o (tvals c R xs) R xs) l).1 = true ∧
                R (out (o (tvals c R xs) R xs) l) =
                  R ((out (o (tvals c R xs) R xs) l).1,
                    xs (out (o (tvals c R xs) R xs) l).1))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
  have hXY : Fintype.card (Tw × Msg → Y) ≠ 0 := Fintype.card_ne_zero
  set cXY : ℝ≥0∞ := (Fintype.card (Tw × Msg → Y) : ℝ≥0∞) with hcXY
  set cXs : ℝ≥0∞ := (Fintype.card (Tw → Msg) : ℝ≥0∞) with hcXs
  have hev : ∀ (R : Tw × Msg → Y) (xs : Tw → Msg),
      (fun l ↦ c (out (o (tvals c R xs) R xs) l).1 = true ∧
        R (out (o (tvals c R xs) R xs) l) =
          R ((out (o (tvals c R xs) R xs) l).1, xs (out (o (tvals c R xs) R xs) l).1)) =
      fun l ↦ e (out (o (tvals c R xs) R xs) l) ∈ (pgMarked c xs R).map e := by
    intro R xs
    funext l
    simp [pgMarked]
  simp only [hev]
  by_cases hN : Fintype.card Y = 1
  · have hb : (1 : ℝ≥0∞) ≤ (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) := by
      have : (Fintype.card Y : ℝ≥0∞)⁻¹ = 1 := by simp [hN]
      calc (1 : ℝ≥0∞) = 1 * 1 := (mul_one 1).symm
        _ ≤ _ := mul_le_mul' (one_le_two_mul_add_one_sq q)
            (le_trans (le_of_eq this.symm) le_self_add)
    refine le_trans ?_ hb
    refine le_trans ?_ hw1
    refine Finset.sum_le_sum fun R _ ↦ ?_
    refine Finset.sum_le_sum fun xs _ ↦ ?_
    calc (cXY⁻¹ * cXs⁻¹) * (w (o (tvals c R xs) R xs) *
            (M (o (tvals c R xs) R xs)).prob (patch F e R)
              (fun l ↦ e (out (o (tvals c R xs) R xs) l) ∈ (pgMarked c xs R).map e))
        ≤ (cXY⁻¹ * cXs⁻¹) * (w (o (tvals c R xs) R xs) * 1) := by
          gcongr
          exact prob_le_one_of_sub (M _) (fun l ↦ e (out (o (tvals c R xs) R xs) l))
            (fun H' T ↦ (M _).prob_sub H' _ T) _ _
      _ = _ := by rw [mul_one]
  · have hnt : Nontrivial Y :=
      Fintype.one_lt_card_iff_nontrivial.1
        (by have := Fintype.card_pos (α := Y); omega)
    obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
    have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
    have hXD : Fintype.card (Tw × Msg → NZ Y) ≠ 0 := Fintype.card_ne_zero
    set cXD : ℝ≥0∞ := (Fintype.card (Tw × Msg → NZ Y) : ℝ≥0∞) with hcXD
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
    set κ : ℝ≥0∞ := cXY⁻¹ * cXs⁻¹ * cXD⁻¹ with hκ
    have hκ' : ∀ x : ℝ≥0∞, cXD * (κ * x) = (cXY⁻¹ * cXs⁻¹) * x := by
      intro x
      calc cXD * (κ * x) = (cXD * cXD⁻¹) * ((cXY⁻¹ * cXs⁻¹) * x) := by rw [hκ]; ring
        _ = _ := by rw [iXD, one_mul]
    have hw : ∑ ω : (Tw → Msg) × (Tw × Msg → Y × NZ Y),
        κ * w (o (tvals c (fun k ↦ (ω.2 k).1) ω.1) (fun k ↦ (ω.2 k).1) ω.1) ≤ 1 := by
      rw [Fintype.sum_prod_type]
      refine le_trans (le_of_eq ?_) hw1
      refine Eq.trans (Finset.sum_congr rfl fun xs _ ↦ ?_)
        (Finset.sum_comm (f := fun (xs : Tw → Msg) (R : Tw × Msg → Y) ↦
          (cXY⁻¹ * cXs⁻¹) * w (o (tvals c R xs) R xs)))
      have := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y)
        (fun H ↦ κ * w (o (tvals c H xs) H xs))
      refine this.trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun R _ ↦ hκ' _
    have hs := (((hidden_pg (Y := Y) c o h1 h2 κ).reweight (fun v ↦ w v.1)).map_emb
        e).search_le hw (fun v ↦ M v.1)
      (fun ω ↦ patch F e (fun k ↦ (ω.2 k).1)) (fun v ↦ patch F e v.2)
      (by
        intro ω z h
        by_cases hz : ∃ p, e p = z
        · obtain ⟨p, rfl⟩ := hz
          rw [patch_apply, patch_apply] at h
          rw [Finset.mem_map']
          simp only [pgMarked, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hc : c p.1 = true
          · refine ⟨hc, ?_⟩
            by_contra hne
            exact h (by simp [pgG, hc, resample, hne])
          · exact (h (by simp [pgG, hc])).elim
        · refine (h ?_).elim
          show patch F e _ z = patch F e (pgG c ω.1 ω.2) z
          rw [patch_of_not_range _ _ _ _ hz, patch_of_not_range _ _ _ _ hz])
      (fun v l ↦ e (out v.1 l))
    refine le_trans (le_of_eq ?_) hs
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun xs _ ↦ ?_
    have e' := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y)
      (fun H ↦ κ * w (o (tvals c H xs) H xs) * (M (o (tvals c H xs) H xs)).prob (patch F e H)
        (fun l ↦ e (out (o (tvals c H xs) H xs) l) ∈ (pgMarked c xs H).map e))
    refine Eq.trans ?_ e'.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [mul_assoc κ]
    exact (hκ' _).symm

/-- **Planted-target multi-target PRE on an embedded random row, weighted, with observations.**
`R ← (Tw × Msg → Y)` uniform, `xs ← (Tw → Msg)` uniform (hidden planted inputs), the oracle is
`patch F e R`; `c` marks the requested tweaks.  The algorithm, its decoding and the weight `w`
depend on the observation `o (tvals c R xs) R xs`: the target values of the requested tweaks, and
(by `h1`, `h2`) otherwise nothing about the requested rows of `R` or the planted inputs of
requested tweaks.  The algorithm outputs `(t, x')` and wins iff `t` is requested and
`R (t, x') = R (t, xs t)`.  The weighted winning probability is at most
`(2q+1)² (1/|Y| + 1/|Msg|)` times the average weight.  (`w` may take the value `⊤`.) -/
theorem pre_embedded_obs_weighted_le {A : Type} (e : Tw × Msg ↪ Z) (F : Z → Y)
    (c : Tw → Bool) (o : (Tw → Option Y) → (Tw × Msg → Y) → (Tw → Msg) → A)
    (h1 : ∀ k : Tw × Msg, c k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y)
      (xs : Tw → Msg) (v : Y), o yv (Function.update R k v) xs = o yv R xs)
    (h2 : ∀ t : Tw, c t = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y)
      (xs : Tw → Msg) (m : Msg), o yv R (Function.update xs t m) = o yv R xs)
    (M : A → HybridModel Z Y Leaf q) (out : A → Leaf → Tw × Msg) (w : A → ℝ≥0∞) :
    ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          (w (o (tvals c R xs) R xs) *
            (M (o (tvals c R xs) R xs)).prob (patch F e R)
              (fun l ↦ c (out (o (tvals c R xs) R xs) l).1 = true ∧
                R (out (o (tvals c R xs) R xs) l) =
                  R ((out (o (tvals c R xs) R xs) l).1,
                    xs (out (o (tvals c R xs) R xs) l).1))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
          ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) *
        ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
          ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
            w (o (tvals c R xs) R xs) := by
  have hc0 : (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hB : (2 * (q : ℝ≥0∞) + 1) ^ 2 *
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) ≠ 0 := by
    refine mul_ne_zero (lt_of_lt_of_le zero_lt_one (one_le_two_mul_add_one_sq q)).ne' ?_
    exact (lt_of_lt_of_le (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)) le_self_add).ne'
  have h := le_mul_sum_of_normalised
    (Ωs := (Tw × Msg → Y) × (Tw → Msg)) _ _ hc0 hB
    (fun r ↦ w (o (tvals c r.1 r.2) r.1 r.2))
    (fun r ↦ (M (o (tvals c r.1 r.2) r.1 r.2)).prob (patch F e r.1)
      (fun l ↦ c (out (o (tvals c r.1 r.2) r.1 r.2) l).1 = true ∧
        r.1 (out (o (tvals c r.1 r.2) r.1 r.2) l) =
          r.1 ((out (o (tvals c r.1 r.2) r.1 r.2) l).1,
            r.2 (out (o (tvals c r.1 r.2) r.1 r.2) l).1)))
    (by
      intro s hs
      rw [Fintype.sum_prod_type] at hs ⊢
      exact pre_embedded_obs_normalised_le e F c o h1 h2 M out (fun a ↦ w a * s) hs)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  exact h

end

end PQ.QROM

#print axioms PQ.QROM.hidden_pg
#print axioms PQ.QROM.pre_embedded_obs_normalised_le
#print axioms PQ.QROM.pre_embedded_obs_weighted_le
