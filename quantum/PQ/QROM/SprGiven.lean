import PQ.QROM.MultiTarget

/-!
# Fixed-target multi-target SPR on an embedded random row, target values given

The oracle `patch F e R : Z → Y` is a fixed function `F` except on the range of an embedding
`e : Tw × Msg ↪ Z`, where it is the uniformly random `R : Tw × Msg → Y`.  A partial target
assignment `c : Tw → Option Msg` is fixed (independently of `R`); the adversary is GIVEN the
values `vals R c` of `R` at the targets (its program and its decoding may depend on them) and
outputs `(t, m')`; it wins iff `c t = some m`, `m' ≠ m` and `R (t, m') = R (t, m)`.

`spr_embedded_given_le`: the winning probability is at most `(2q+1)² / |Y|`.

Coupling: as in `mt_spr_fixed_le` (worlds `τ : Tw × Msg → Y × NZ Y`, `R = Prod.fst ∘ τ`, the
target coordinates are kept and every other point of a tweak with a target is resampled away from
the target value); the view is `(vals R c, G)`, which does not depend on a non-target coordinate
except through its resampled value.  The marked set is transported to `Z` along `e`.
-/

open ENNReal Finset

namespace PQ.QROM

section

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]

/-- `R` on the range of `e`, `F` elsewhere. -/
noncomputable def patch (F : Z → Y) (e : Tw × Msg ↪ Z) (R : Tw × Msg → Y) : Z → Y := fun z ↦
  if h : ∃ p, e p = z then R (Classical.choose h) else F z

omit [Fintype Z] [DecidableEq Tw] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] in
@[simp]
theorem patch_apply (F : Z → Y) (e : Tw × Msg ↪ Z) (R : Tw × Msg → Y) (p : Tw × Msg) :
    patch F e R (e p) = R p := by
  have h : ∃ p', e p' = e p := ⟨p, rfl⟩
  unfold patch
  simp only [h, ↓reduceDIte]
  rw [e.injective (Classical.choose_spec h)]

omit [Fintype Z] [DecidableEq Tw] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] in
theorem patch_of_not_range (F : Z → Y) (e : Tw × Msg ↪ Z) (R : Tw × Msg → Y) (z : Z)
    (h : ¬ ∃ p, e p = z) : patch F e R z = F z := by
  unfold patch
  simp only [h, ↓reduceDIte]

/-- The values of `R` at the targets. -/
def vals (R : Tw × Msg → Y) (c : Tw → Option Msg) : Tw → Option Y :=
  fun t ↦ (c t).map fun m ↦ R (t, m)

/-- The marked set: non-target points of a tweak with a target that collide with the target. -/
def sgMarked (c : Tw → Option Msg) (R : Tw × Msg → Y) : Finset (Tw × Msg) :=
  univ.filter fun k ↦ ∃ m, c k.1 = some m ∧ k.2 ≠ m ∧ R k = R (k.1, m)

variable [AddCommGroup Y]

/-- The hybrid function: targets and tweaks without a target are kept; every other point is
resampled away from the target value of its tweak. -/
def sgG (c : Tw → Option Msg) (τ : Tw × Msg → Y × NZ Y) (j : Tw × Msg) : Y :=
  (c j.1).elim (τ j).1 fun m ↦ if j.2 = m then (τ j).1 else resample (τ (j.1, m)).1 (τ j)

/-- Transporting a hidden marked set along an embedding of the domain. -/
theorem Hidden.map_emb {Ω V X Z' : Type} [Fintype Ω] [DecidableEq X] [DecidableEq Z']
    {w : Ω → ℝ≥0∞} {view : Ω → V} {S : Ω → Finset X} {ε : ℝ≥0∞} (h : Hidden w view S ε)
    (e : X ↪ Z') : Hidden w view (fun ω ↦ (S ω).map e) ε := by
  intro z φ
  by_cases hz : ∃ p, e p = z
  · obtain ⟨p, rfl⟩ := hz
    simpa only [Finset.mem_map'] using h p φ
  · have : ∀ ω, z ∉ (S ω).map e := by
      intro ω hm
      obtain ⟨p, _, hp⟩ := Finset.mem_map.1 hm
      exact hz ⟨p, hp⟩
    simp [this]

/-- Given the view `(vals R c, G)`, every point is marked with probability at most `1/|Y|`. -/
theorem hidden_sg (c : Tw → Option Msg) (κ : ℝ≥0∞) :
    Hidden (Ω := Tw × Msg → Y × NZ Y) (fun _ ↦ κ)
      (fun τ ↦ (vals (fun k ↦ (τ k).1) c, sgG c τ))
      (fun τ ↦ sgMarked c (fun k ↦ (τ k).1)) (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  cases hc : c k.1 with
  | none => simp [sgMarked, hc]
  | some m =>
    by_cases hk : k.2 = m
    · simp [sgMarked, hc, hk]
    · have hne : ∀ t' m', c t' = some m' → (t', m') ≠ k := by
        intro t' m' h heq
        have h1 : k.1 = t' := by rw [← heq]
        have h2 : k.2 = m' := by rw [← heq]
        rw [h1, h] at hc
        exact hk (h2.trans (Option.some.inj hc))
      have hvals : ∀ (τ : Tw × Msg → Y × NZ Y) (t : Y × NZ Y),
          vals (fun j ↦ (Function.update τ k t j).1) c = vals (fun j ↦ (τ j).1) c := by
        intro τ t
        funext t'
        cases hct : c t' with
        | none => simp [vals, hct]
        | some m' => simp [vals, hct, Function.update_of_ne (hne t' m' hct)]
      have e := sum_marked_view (X := Tw × Msg) k (fun τ ↦ (τ (k.1, m)).1)
        (fun τ t ↦ by simp [Function.update_of_ne (hne k.1 m hc)])
        (sgG c) (fun τ ↦ by simp [sgG, hc, hk])
        (fun τ t j hj ↦ by
          cases hcj : c j.1 with
          | none => simp [sgG, hcj, Function.update_of_ne hj]
          | some m' =>
            simp [sgG, hcj, Function.update_of_ne hj, Function.update_of_ne (hne j.1 m' hcj)])
        (fun τ g ↦ κ * φ (vals (fun j ↦ (τ j).1) c, g))
        (fun τ t g ↦ by simp only [hvals])
      have hmem : ∀ τ : Tw × Msg → Y × NZ Y,
          k ∈ sgMarked c (fun j ↦ (τ j).1) ↔ (τ k).1 = (τ (k.1, m)).1 := by
        intro τ
        simp [sgMarked, hc, hk]
      refine le_of_eq ?_
      rw [← e]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      simp only [hmem]
      split_ifs <;> simp

variable {Leaf : Type} {q : ℕ}

/-- **Fixed-target multi-target SPR on an embedded random row, target values given.**  The oracle
is `patch F e R` (`F` fixed, `R ← (Tw × Msg → Y)` uniform on the range of `e`); `c` is any fixed
partial target assignment; the `q`-query algorithm `M (vals R c)` and its decoding may depend on
the values of `R` at the targets; it outputs `(t, m')` and wins iff `c t = some m`, `m' ≠ m` and
`R (t, m') = R (t, m)`.  The winning probability is at most `(2q+1)² / |Y|`. -/
theorem spr_embedded_given_le (e : Tw × Msg ↪ Z) (F : Z → Y) (c : Tw → Option Msg)
    (M : (Tw → Option Y) → HybridModel Z Y Leaf q) (out : (Tw → Option Y) → Leaf → Tw × Msg) :
    ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ *
        (M (vals R c)).prob (patch F e R)
          (fun l ↦ ∃ m, c (out (vals R c) l).1 = some m ∧ (out (vals R c) l).2 ≠ m ∧
            R (out (vals R c) l) = R ((out (vals R c) l).1, m)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  have hXY : Fintype.card (Tw × Msg → Y) ≠ 0 := Fintype.card_ne_zero
  set cXY : ℝ≥0∞ := (Fintype.card (Tw × Msg → Y) : ℝ≥0∞) with hcXY
  have iXY : cXY * cXY⁻¹ = 1 := natCast_mul_inv_cancel hXY
  have hev : ∀ R : Tw × Msg → Y,
      (fun l ↦ ∃ m, c (out (vals R c) l).1 = some m ∧ (out (vals R c) l).2 ≠ m ∧
        R (out (vals R c) l) = R ((out (vals R c) l).1, m)) =
      fun l ↦ e (out (vals R c) l) ∈ (sgMarked c R).map e := by
    intro R
    funext l
    simp [sgMarked]
  simp only [hev]
  by_cases hN : Fintype.card Y = 1
  · rw [hN, Nat.cast_one, div_one]
    refine le_trans ?_ (one_le_two_mul_add_one_sq q)
    calc ∑ R : Tw × Msg → Y, cXY⁻¹ * (M (vals R c)).prob (patch F e R)
            (fun l ↦ e (out (vals R c) l) ∈ (sgMarked c R).map e)
        ≤ ∑ _R : Tw × Msg → Y, cXY⁻¹ * 1 := by
          gcongr with R _
          exact prob_le_one_of_sub (M (vals R c)) (fun l ↦ e (out (vals R c) l))
            (fun H' T ↦ (M (vals R c)).prob_sub H' _ T) _ _
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcXY]
          exact natCast_mul_inv_cancel hXY
  · have hnt : Nontrivial Y :=
      Fintype.one_lt_card_iff_nontrivial.1
        (by have := Fintype.card_pos (α := Y); omega)
    obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
    have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
    have hXD : Fintype.card (Tw × Msg → NZ Y) ≠ 0 := Fintype.card_ne_zero
    set cXD : ℝ≥0∞ := (Fintype.card (Tw × Msg → NZ Y) : ℝ≥0∞) with hcXD
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
    set κ : ℝ≥0∞ := cXY⁻¹ * cXD⁻¹ with hκ
    have hw : ∑ _τ : Tw × Msg → Y × NZ Y, κ ≤ 1 := by
      have := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y) (fun _ ↦ κ)
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc cXD * (cXY * κ) = (cXY * cXY⁻¹) * (cXD * cXD⁻¹) := by rw [hκ]; ring
        _ ≤ 1 := by rw [iXY, iXD, mul_one]
    have hs := ((hidden_sg (Y := Y) c κ).map_emb e).search_le hw (fun v ↦ M v.1)
      (fun τ ↦ patch F e (fun k ↦ (τ k).1)) (fun v ↦ patch F e v.2)
      (by
        intro τ z h
        by_cases hz : ∃ p, e p = z
        · obtain ⟨p, rfl⟩ := hz
          rw [patch_apply, patch_apply] at h
          rw [Finset.mem_map']
          simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hc : c p.1 with
          | none => exact (h (by simp [sgG, hc])).elim
          | some m =>
            by_cases hp : p.2 = m
            · exact (h (by simp [sgG, hc, hp])).elim
            · refine ⟨m, rfl, hp, ?_⟩
              by_contra hne
              exact h (by simp [sgG, hc, hp, resample, hne])
        · refine (h ?_).elim
          show patch F e _ z = patch F e (sgG c τ) z
          rw [patch_of_not_range _ _ _ _ hz, patch_of_not_range _ _ _ _ hz])
      (fun v l ↦ e (out v.1 l))
    rw [div_eq_mul_inv]
    refine le_trans (le_of_eq ?_) hs
    have e' := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y)
      (fun H ↦ κ * (M (vals H c)).prob (patch F e H)
        (fun l ↦ e (out (vals H c) l) ∈ (sgMarked c H).map e))
    refine Eq.trans ?_ e'.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    calc cXY⁻¹ * (M (vals R c)).prob (patch F e R)
          (fun l ↦ e (out (vals R c) l) ∈ (sgMarked c R).map e)
        = (cXD * cXD⁻¹) * (cXY⁻¹ * (M (vals R c)).prob (patch F e R)
            (fun l ↦ e (out (vals R c) l) ∈ (sgMarked c R).map e)) := by rw [iXD, one_mul]
      _ = _ := by rw [hκ]; ring

/-! ### Weighted forms, general observations -/

/-- Reweighting the worlds by a function of the view preserves hiddenness. -/
theorem Hidden.reweight {Ω V X : Type} [Fintype Ω] [DecidableEq X] {κ : ℝ≥0∞} {view : Ω → V}
    {S : Ω → Finset X} {ε : ℝ≥0∞} (h : Hidden (fun _ ↦ κ) view S ε) (g : V → ℝ≥0∞) :
    Hidden (fun ω ↦ κ * g (view ω)) view S ε := by
  intro k φ
  have h' := h k (fun v ↦ g v * φ v)
  refine le_trans (le_of_eq ?_) (le_trans h' (le_of_eq ?_))
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    split_ifs
    · ring
    · simp
  · congr 1
    exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- `hidden_sg` for a general observation `obs R` of the random row that does not depend on the
non-target points of the tweaks that have a target. -/
theorem hidden_sg_obs {A : Type} (c : Tw → Option Msg) (obs : (Tw × Msg → Y) → A)
    (hobs : ∀ (k : Tw × Msg) (m : Msg), c k.1 = some m → k.2 ≠ m →
      ∀ (R : Tw × Msg → Y) (v : Y), obs (Function.update R k v) = obs R) (κ : ℝ≥0∞) :
    Hidden (Ω := Tw × Msg → Y × NZ Y) (fun _ ↦ κ)
      (fun τ ↦ (obs (fun k ↦ (τ k).1), sgG c τ))
      (fun τ ↦ sgMarked c (fun k ↦ (τ k).1)) (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  intro k φ
  cases hc : c k.1 with
  | none => simp [sgMarked, hc]
  | some m =>
    by_cases hk : k.2 = m
    · simp [sgMarked, hc, hk]
    · have hne : ∀ t' m', c t' = some m' → (t', m') ≠ k := by
        intro t' m' h heq
        have h1 : k.1 = t' := by rw [← heq]
        have h2 : k.2 = m' := by rw [← heq]
        rw [h1, h] at hc
        exact hk (h2.trans (Option.some.inj hc))
      have hvals : ∀ (τ : Tw × Msg → Y × NZ Y) (t : Y × NZ Y),
          obs (fun j ↦ (Function.update τ k t j).1) = obs (fun j ↦ (τ j).1) := by
        intro τ t
        have : (fun j ↦ (Function.update τ k t j).1) =
            Function.update (fun j ↦ (τ j).1) k t.1 := by
          funext j
          by_cases hj : j = k
          · rw [hj]; simp
          · simp [Function.update_of_ne hj]
        rw [this, hobs k m hc hk]
      have e := sum_marked_view (X := Tw × Msg) k (fun τ ↦ (τ (k.1, m)).1)
        (fun τ t ↦ by simp [Function.update_of_ne (hne k.1 m hc)])
        (sgG c) (fun τ ↦ by simp [sgG, hc, hk])
        (fun τ t j hj ↦ by
          cases hcj : c j.1 with
          | none => simp [sgG, hcj, Function.update_of_ne hj]
          | some m' =>
            simp [sgG, hcj, Function.update_of_ne hj, Function.update_of_ne (hne j.1 m' hcj)])
        (fun τ g ↦ κ * φ (obs (fun j ↦ (τ j).1), g))
        (fun τ t g ↦ by simp only [hvals])
      have hmem : ∀ τ : Tw × Msg → Y × NZ Y,
          k ∈ sgMarked c (fun j ↦ (τ j).1) ↔ (τ k).1 = (τ (k.1, m)).1 := by
        intro τ
        simp [sgMarked, hc, hk]
      refine le_of_eq ?_
      rw [← e]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      simp only [hmem]
      split_ifs <;> simp

/-- Normalised weighted form: if the weight has average at most one, the weighted winning
probability is at most `(2q+1)² / |Y|`. -/
theorem spr_embedded_obs_normalised_le {A : Type} (e : Tw × Msg ↪ Z) (F : Z → Y)
    (c : Tw → Option Msg) (obs : (Tw × Msg → Y) → A)
    (hobs : ∀ (k : Tw × Msg) (m : Msg), c k.1 = some m → k.2 ≠ m →
      ∀ (R : Tw × Msg → Y) (v : Y), obs (Function.update R k v) = obs R)
    (M : A → HybridModel Z Y Leaf q) (out : A → Leaf → Tw × Msg) (w : A → ℝ≥0∞)
    (hw1 : ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * w (obs R) ≤ 1) :
    ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (w (obs R) *
        (M (obs R)).prob (patch F e R) (fun l ↦ ∃ m, c (out (obs R) l).1 = some m ∧
          (out (obs R) l).2 ≠ m ∧ R (out (obs R) l) = R ((out (obs R) l).1, m))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) := by
  have hXY : Fintype.card (Tw × Msg → Y) ≠ 0 := Fintype.card_ne_zero
  set cXY : ℝ≥0∞ := (Fintype.card (Tw × Msg → Y) : ℝ≥0∞) with hcXY
  have iXY : cXY * cXY⁻¹ = 1 := natCast_mul_inv_cancel hXY
  have hev : ∀ R : Tw × Msg → Y,
      (fun l ↦ ∃ m, c (out (obs R) l).1 = some m ∧ (out (obs R) l).2 ≠ m ∧
        R (out (obs R) l) = R ((out (obs R) l).1, m)) =
      fun l ↦ e (out (obs R) l) ∈ (sgMarked c R).map e := by
    intro R
    funext l
    simp [sgMarked]
  simp only [hev]
  by_cases hN : Fintype.card Y = 1
  · rw [hN, Nat.cast_one, div_one]
    refine le_trans ?_ (one_le_two_mul_add_one_sq q)
    refine le_trans ?_ hw1
    refine Finset.sum_le_sum fun R _ ↦ ?_
    calc cXY⁻¹ * (w (obs R) * (M (obs R)).prob (patch F e R)
            (fun l ↦ e (out (obs R) l) ∈ (sgMarked c R).map e))
        ≤ cXY⁻¹ * (w (obs R) * 1) := by
          gcongr
          exact prob_le_one_of_sub (M (obs R)) (fun l ↦ e (out (obs R) l))
            (fun H' T ↦ (M (obs R)).prob_sub H' _ T) _ _
      _ = cXY⁻¹ * w (obs R) := by rw [mul_one]
  · have hnt : Nontrivial Y :=
      Fintype.one_lt_card_iff_nontrivial.1
        (by have := Fintype.card_pos (α := Y); omega)
    obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
    have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
    have hXD : Fintype.card (Tw × Msg → NZ Y) ≠ 0 := Fintype.card_ne_zero
    set cXD : ℝ≥0∞ := (Fintype.card (Tw × Msg → NZ Y) : ℝ≥0∞) with hcXD
    have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
    set κ : ℝ≥0∞ := cXY⁻¹ * cXD⁻¹ with hκ
    have hκ' : ∀ x : ℝ≥0∞, cXD * (κ * x) = cXY⁻¹ * x := by
      intro x
      calc cXD * (κ * x) = (cXD * cXD⁻¹) * (cXY⁻¹ * x) := by rw [hκ]; ring
        _ = cXY⁻¹ * x := by rw [iXD, one_mul]
    have hw : ∑ τ : Tw × Msg → Y × NZ Y, κ * w (obs (fun k ↦ (τ k).1)) ≤ 1 := by
      have := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y) (fun H ↦ κ * w (obs H))
      rw [this, Finset.mul_sum]
      exact le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ hκ' _)) hw1
    have hs := (((hidden_sg_obs (Y := Y) c obs hobs κ).reweight (fun v ↦ w v.1)).map_emb
        e).search_le hw (fun v ↦ M v.1)
      (fun τ ↦ patch F e (fun k ↦ (τ k).1)) (fun v ↦ patch F e v.2)
      (by
        intro τ z h
        by_cases hz : ∃ p, e p = z
        · obtain ⟨p, rfl⟩ := hz
          rw [patch_apply, patch_apply] at h
          rw [Finset.mem_map']
          simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hc : c p.1 with
          | none => exact (h (by simp [sgG, hc])).elim
          | some m =>
            by_cases hp : p.2 = m
            · exact (h (by simp [sgG, hc, hp])).elim
            · refine ⟨m, rfl, hp, ?_⟩
              by_contra hne
              exact h (by simp [sgG, hc, hp, resample, hne])
        · refine (h ?_).elim
          show patch F e _ z = patch F e (sgG c τ) z
          rw [patch_of_not_range _ _ _ _ hz, patch_of_not_range _ _ _ _ hz])
      (fun v l ↦ e (out v.1 l))
    rw [div_eq_mul_inv]
    refine le_trans (le_of_eq ?_) hs
    have e' := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y)
      (fun H ↦ κ * w (obs H) * (M (obs H)).prob (patch F e H)
        (fun l ↦ e (out (obs H) l) ∈ (sgMarked c H).map e))
    refine Eq.trans ?_ e'.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [mul_assoc, hκ']

/-- **Weighted form, general observation.**  As `spr_embedded_given_le`, but the adversary's
program, its decoding and a nonnegative weight `w` depend on an observation `obs R` of the random
row that does not depend on the non-target points of the tweaks that have a target.  The weighted
winning probability is at most `(2q+1)² / |Y|` times the average weight.  (`w` may take the
value `⊤`.) -/
theorem spr_embedded_obs_weighted_le {A : Type} (e : Tw × Msg ↪ Z) (F : Z → Y)
    (c : Tw → Option Msg) (obs : (Tw × Msg → Y) → A)
    (hobs : ∀ (k : Tw × Msg) (m : Msg), c k.1 = some m → k.2 ≠ m →
      ∀ (R : Tw × Msg → Y) (v : Y), obs (Function.update R k v) = obs R)
    (M : A → HybridModel Z Y Leaf q) (out : A → Leaf → Tw × Msg) (w : A → ℝ≥0∞) :
    ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (w (obs R) *
        (M (obs R)).prob (patch F e R) (fun l ↦ ∃ m, c (out (obs R) l).1 = some m ∧
          (out (obs R) l).2 ≠ m ∧ R (out (obs R) l) = R ((out (obs R) l).1, m))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) *
        ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * w (obs R) := by
  set cXY : ℝ≥0∞ := (Fintype.card (Tw × Msg → Y) : ℝ≥0∞) with hcXY
  set Wt : ℝ≥0∞ := ∑ R : Tw × Msg → Y, cXY⁻¹ * w (obs R) with hWt
  set B : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) with hB
  have hc0 : cXY⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  by_cases h0 : Wt = 0
  · have hz : ∀ R : Tw × Msg → Y, w (obs R) = 0 := by
      intro R
      have := (Finset.sum_eq_zero_iff.1 h0) R (Finset.mem_univ R)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc0
      · exact h
    simp [hz]
  by_cases htop : Wt = ⊤
  · have hBpos : B ≠ 0 := by
      have h1 : (2 * (q : ℝ≥0∞) + 1) ^ 2 ≠ 0 :=
        (lt_of_lt_of_le zero_lt_one (one_le_two_mul_add_one_sq q)).ne'
      exact (ENNReal.div_pos h1 (ENNReal.natCast_ne_top _)).ne'
    rw [htop, ENNReal.mul_top hBpos]
    exact le_top
  · have iW : Wt⁻¹ * Wt = 1 := ENNReal.inv_mul_cancel h0 htop
    have hn := spr_embedded_obs_normalised_le e F c obs hobs M out (fun a ↦ w a * Wt⁻¹)
      (le_of_eq (by
        calc ∑ R : Tw × Msg → Y, cXY⁻¹ * (w (obs R) * Wt⁻¹)
            = Wt⁻¹ * Wt := by
              rw [hWt, Finset.mul_sum]
              exact Finset.sum_congr rfl fun R _ ↦ by ring
          _ = 1 := iW))
    calc _ = (∑ R : Tw × Msg → Y, cXY⁻¹ * (w (obs R) * Wt⁻¹ *
          (M (obs R)).prob (patch F e R) (fun l ↦ ∃ m, c (out (obs R) l).1 = some m ∧
            (out (obs R) l).2 ≠ m ∧ R (out (obs R) l) = R ((out (obs R) l).1, m)))) * Wt := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun R _ ↦ ?_
          calc cXY⁻¹ * (w (obs R) * (M (obs R)).prob (patch F e R) _)
              = cXY⁻¹ * (w (obs R) * (M (obs R)).prob (patch F e R) _) * (Wt⁻¹ * Wt) := by
                rw [iW, mul_one]
            _ = _ := by ring
      _ ≤ B * Wt := mul_le_mul' hn le_rfl

/-- **Weighted form, target values given.**  The weight `w` depends on `R` only through the
target values `vals R c`.  (`w` may take the value `⊤`.) -/
theorem spr_embedded_given_weighted_le (e : Tw × Msg ↪ Z) (F : Z → Y) (c : Tw → Option Msg)
    (M : (Tw → Option Y) → HybridModel Z Y Leaf q) (out : (Tw → Option Y) → Leaf → Tw × Msg)
    (w : (Tw → Option Y) → ℝ≥0∞) :
    ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (w (vals R c) *
        (M (vals R c)).prob (patch F e R) (fun l ↦ ∃ m, c (out (vals R c) l).1 = some m ∧
          (out (vals R c) l).2 ≠ m ∧ R (out (vals R c) l) = R ((out (vals R c) l).1, m))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) *
        ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * w (vals R c) :=
  spr_embedded_obs_weighted_le e F c (fun R ↦ vals R c)
    (by
      intro k m hc hk R v
      funext t'
      cases hct : c t' with
      | none => simp [vals, hct]
      | some m' =>
        have hne : (t', m') ≠ k := by
          intro heq
          have h1 : k.1 = t' := by rw [← heq]
          have h2 : k.2 = m' := by rw [← heq]
          rw [h1, hct] at hc
          exact hk (h2.trans (Option.some.inj hc))
        simp [vals, hct, Function.update_of_ne hne])
    M out w

/-- **Weighted form, target values and collection values given.**  The adversary is additionally
given the values of `R` on a fixed set `Cq` of points lying in tweaks WITHOUT a target
(`c t = none`); its program, its decoding and the weight may depend on
`(vals R c, R restricted to Cq)`.  The bound is unchanged. -/
theorem spr_embedded_given_coll_weighted_le (e : Tw × Msg ↪ Z) (F : Z → Y)
    (c : Tw → Option Msg) (Cq : Finset (Tw × Msg)) (hCq : ∀ p ∈ Cq, c p.1 = none)
    (M : (Tw → Option Y) × (Cq → Y) → HybridModel Z Y Leaf q)
    (out : (Tw → Option Y) × (Cq → Y) → Leaf → Tw × Msg)
    (w : (Tw → Option Y) × (Cq → Y) → ℝ≥0∞) :
    ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ *
        (w (vals R c, fun p : Cq ↦ R p.1) *
          (M (vals R c, fun p : Cq ↦ R p.1)).prob (patch F e R)
            (fun l ↦ ∃ m, c (out (vals R c, fun p : Cq ↦ R p.1) l).1 = some m ∧
              (out (vals R c, fun p : Cq ↦ R p.1) l).2 ≠ m ∧
              R (out (vals R c, fun p : Cq ↦ R p.1) l) =
                R ((out (vals R c, fun p : Cq ↦ R p.1) l).1, m))) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) *
        ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ *
          w (vals R c, fun p : Cq ↦ R p.1) :=
  spr_embedded_obs_weighted_le e F c (fun R ↦ (vals R c, fun p : Cq ↦ R p.1))
    (by
      intro k m hc hk R v
      refine Prod.ext ?_ ?_
      · funext t'
        cases hct : c t' with
        | none => simp [vals, hct]
        | some m' =>
          have hne : (t', m') ≠ k := by
            intro heq
            have h1 : k.1 = t' := by rw [← heq]
            have h2 : k.2 = m' := by rw [← heq]
            rw [h1, hct] at hc
            exact hk (h2.trans (Option.some.inj hc))
          simp [vals, hct, Function.update_of_ne hne]
      · funext p
        have hne : p.1 ≠ k := by
          intro heq
          have := hCq p.1 p.2
          rw [heq, hc] at this
          exact Option.some_ne_none m this
        simp [Function.update_of_ne hne])
    M out w

end

end PQ.QROM

#print axioms PQ.QROM.spr_embedded_given_le
#print axioms PQ.QROM.spr_embedded_obs_weighted_le
#print axioms PQ.QROM.spr_embedded_given_weighted_le
#print axioms PQ.QROM.spr_embedded_given_coll_weighted_le
