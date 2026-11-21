import PQ.QROM.PreGiven
import PQ.QROM.Distinguish

/-!
# Undetectability on an embedded random row, with observations and weights

Embedded-row setting of `pre_embedded_obs_weighted_le`: the oracle is `patch F e R` (`F` fixed,
`R : Tw × Msg → Y` uniform on the range of `e : Tw × Msg ↪ Z`); `c : Tw → Bool` marks the
requested tweaks.

* Real world: `xs : Tw → Msg` uniform and hidden; the target value of a requested tweak `t` is
  `R (t, xs t)` (`tvals c R xs`).
* Ideal world: `ys : Tw → Y` uniform and independent of `R`; the target value of a requested tweak
  `t` is `ys t` (`yvals c ys`).

In both worlds the algorithm, the weight `w` and the event `E` depend on an observation
`o targets R` that does not depend on the requested rows of `R` (hypothesis `h1`).

`ud_embedded_real_le_ideal_add`, `ud_embedded_ideal_le_real_add`: the weighted probabilities of
the two worlds differ by at most `4 q / √|Msg|` TIMES THE AVERAGE WEIGHT (the additive error
scales with the weight, so the bounds can be summed over the leaves of a first phase).
`ud_embedded_weight_eq`: the average weight is the same in both worlds.

Coupling (as in `PQ/QROM/Distinguish.lean`, UD): worlds `(xs, ys, R)` uniform; the ideal function
is `R`; the real function is `udRep c xs ys R` (`R` reprogrammed to `ys t` at the hidden points
`(t, xs t)` of requested tweaks), which is uniform and has target values `ys`.  The two functions
differ only at the hidden points, which are `1/|Msg|`-hidden from the view `(ys, R)`.
-/

open ENNReal Finset

set_option linter.unusedSectionVars false

namespace PQ.QROM

section

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]

/-- The target values of the ideal world: `ys t` for every requested tweak. -/
def yvals (c : Tw → Bool) (ys : Tw → Y) : Tw → Option Y :=
  fun t ↦ if c t = true then some (ys t) else none

/-- `R` reprogrammed to `ys t` at the hidden point `(t, xs t)` of every requested tweak. -/
def udRep (c : Tw → Bool) (xs : Tw → Msg) (ys : Tw → Y) (R : Tw × Msg → Y) : Tw × Msg → Y :=
  fun p ↦ if c p.1 = true ∧ p.2 = xs p.1 then ys p.1 else R p

/-- The hidden points of the requested tweaks. -/
def udgMarked (c : Tw → Bool) (xs : Tw → Msg) : Finset (Tw × Msg) :=
  univ.filter fun p ↦ c p.1 = true ∧ p.2 = xs p.1

/-- Exchange the values at the hidden points of requested tweaks with `ys`. -/
def udgSwap (c : Tw → Bool) (xs : Tw → Msg) (v : (Tw → Y) × (Tw × Msg → Y)) :
    (Tw → Y) × (Tw × Msg → Y) :=
  (fun t ↦ if c t = true then v.2 (t, xs t) else v.1 t, udRep c xs v.1 v.2)

theorem udgSwap_involutive (c : Tw → Bool) (xs : Tw → Msg) :
    Function.Involutive (udgSwap (Y := Y) c xs) := by
  rintro ⟨ys, R⟩
  refine Prod.ext (funext fun t ↦ ?_) (funext fun p ↦ ?_)
  · by_cases h : c t = true <;> simp [udgSwap, udRep, h]
  · by_cases h : c p.1 = true ∧ p.2 = xs p.1
    · obtain ⟨h1, h2⟩ := h
      have : (p.1, xs p.1) = p := by rw [← h2]
      simp [udgSwap, udRep, h1, h2, this]
    · simp [udgSwap, udRep, h]

/-- An observation that ignores single points of requested rows ignores the requested rows. -/
theorem obs_congr_of_update {A : Type} (c : Tw → Bool)
    (o : (Tw → Option Y) → (Tw × Msg → Y) → A)
    (h1 : ∀ k : Tw × Msg, c k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y) (v : Y),
      o yv (Function.update R k v) = o yv R)
    (yv : Tw → Option Y) (R R' : Tw × Msg → Y) (h : ∀ p, c p.1 ≠ true → R p = R' p) :
    o yv R' = o yv R := by
  classical
  have key : ∀ s : Finset (Tw × Msg), (∀ p ∈ s, c p.1 = true) →
      o yv (fun p ↦ if p ∈ s then R' p else R p) = o yv R := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      have : (fun p ↦ if p ∈ insert a s then R' p else R p) =
          Function.update (fun p ↦ if p ∈ s then R' p else R p) a (R' a) := by
        funext p
        by_cases hp : p = a
        · rw [hp]; simp
        · simp [Finset.mem_insert, hp]
      rw [this, h1 a (hs a (Finset.mem_insert_self a s)),
        ih fun p hp ↦ hs p (Finset.mem_insert_of_mem hp)]
  have hfin := key (Finset.univ.filter fun p : Tw × Msg ↦ c p.1 = true) (by
    intro p hp
    exact (Finset.mem_filter.1 hp).2)
  rw [← hfin]
  congr 1
  funext p
  by_cases hp : c p.1 = true
  · simp [hp]
  · simp [hp, h p hp]

variable [AddCommGroup Y] {Leaf : Type} {q : ℕ}

section Core

variable {A : Type} (e : Tw × Msg ↪ Z) (F : Z → Y) (c : Tw → Bool)
  (o : (Tw → Option Y) → (Tw × Msg → Y) → A)
  (h1 : ∀ k : Tw × Msg, c k.1 = true → ∀ (yv : Tw → Option Y) (R : Tw × Msg → Y) (v : Y),
    o yv (Function.update R k v) = o yv R)

include h1 in
theorem obs_udRep (xs : Tw → Msg) (ys : Tw → Y) (R : Tw × Msg → Y) :
    o (tvals c (udRep c xs ys R) xs) (udRep c xs ys R) = o (yvals c ys) R := by
  have e1 : tvals c (udRep c xs ys R) xs = yvals c ys := by
    funext t
    by_cases h : c t = true <;> simp [tvals, yvals, udRep, h]
  rw [e1]
  exact obs_congr_of_update c o h1 _ R _ fun p hp ↦ by simp [udRep, hp]

/-- The ideal side of the coupling. -/
theorem ud_coupling_ideal [Nonempty Msg] (Gf : (Tw → Y) → (Tw × Msg → Y) → ℝ≥0∞) :
    ∑ ω : (Tw → Msg) × ((Tw → Y) × (Tw × Msg → Y)),
        ((Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹)) * Gf ω.2.1 ω.2.2 =
      ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
          Gf ys R := by
  have iXs := card_mul_inv_cancel (Tw → Msg)
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ys _ ↦ ?_
  calc (Fintype.card (Tw → Msg) : ℝ≥0∞) * (((Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹)) * Gf ys R)
      = ((Fintype.card (Tw → Msg) : ℝ≥0∞) * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          (((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
            Gf ys R) := by ring
    _ = _ := by rw [iXs, one_mul]

include h1 in
/-- The real side of the coupling: `udRep c xs ys R` is uniform with target values `ys`. -/
theorem ud_coupling_real (Φ : A → (Tw × Msg → Y) → ℝ≥0∞) :
    ∑ ω : (Tw → Msg) × ((Tw → Y) × (Tw × Msg → Y)),
        ((Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹)) *
          Φ (o (yvals c ω.2.1) ω.2.2) (udRep c ω.1 ω.2.1 ω.2.2) =
      ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          Φ (o (tvals c R xs) R) R := by
  have iYs := card_mul_inv_cancel (Tw → Y)
  set κ : ℝ≥0∞ := (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
    (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹) with hκ
  rw [Fintype.sum_prod_type]
  refine Eq.trans (Finset.sum_congr rfl fun xs _ ↦ ?_)
    (Finset.sum_comm (f := fun (xs : Tw → Msg) (R : Tw × Msg → Y) ↦
      ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
        Φ (o (tvals c R xs) R) R))
  have hsw := Equiv.sum_comp (udgSwap_involutive (Y := Y) c xs).toPerm
    (fun v : (Tw → Y) × (Tw × Msg → Y) ↦ κ * Φ (o (tvals c v.2 xs) v.2) v.2)
  simp only [Function.Involutive.coe_toPerm] at hsw
  have hL : ∀ v : (Tw → Y) × (Tw × Msg → Y),
      κ * Φ (o (yvals c v.1) v.2) (udRep c xs v.1 v.2) =
        κ * Φ (o (tvals c (udgSwap c xs v).2 xs) (udgSwap c xs v).2) (udgSwap c xs v).2 := by
    intro v
    show _ = κ * Φ (o (tvals c (udRep c xs v.1 v.2) xs) (udRep c xs v.1 v.2)) (udRep c xs v.1 v.2)
    rw [obs_udRep c o h1]
  rw [Finset.sum_congr rfl fun v _ ↦ hL v, hsw, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ ↦ ?_
  calc (Fintype.card (Tw → Y) : ℝ≥0∞) * (κ * Φ (o (tvals c R xs) R) R)
      = ((Fintype.card (Tw → Y) : ℝ≥0∞) * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
          (((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
            Φ (o (tvals c R xs) R) R) := by rw [hκ]; ring
    _ = _ := by rw [iYs, one_mul]

include h1 in
/-- **The average weight is the same in both worlds.** -/
theorem ud_embedded_weight_eq [Nonempty Msg] (w : A → ℝ≥0∞) :
    ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          w (o (tvals c R xs) R) =
      ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
          w (o (yvals c ys) R) := by
  rw [← ud_coupling_real c o h1 (fun a _ ↦ w a),
    ← ud_coupling_ideal (fun ys R ↦ w (o (yvals c ys) R))]

variable (M : A → HybridModel Z Y Leaf q) (E : A → Leaf → Prop) (w : A → ℝ≥0∞)

include h1 in
/-- Normalised form: if the average weight is at most one, the two worlds are
`4 q / √|Msg|`-close, in both directions. -/
theorem ud_embedded_normalised [Nonempty Z] [Nonempty Msg]
    (hW : ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
      ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
        w (o (yvals c ys) R) ≤ 1) :
    (∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          (w (o (tvals c R xs) R) *
            (M (o (tvals c R xs) R)).prob (patch F e R) (E (o (tvals c R xs) R))) ≤
      ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
          (w (o (yvals c ys) R) *
            (M (o (yvals c ys) R)).prob (patch F e R) (E (o (yvals c ys) R))) +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ∧
    (∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
          (w (o (yvals c ys) R) *
            (M (o (yvals c ys) R)).prob (patch F e R) (E (o (yvals c ys) R))) ≤
      ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
          (w (o (tvals c R xs) R) *
            (M (o (tvals c R xs) R)).prob (patch F e R) (E (o (tvals c R xs) R))) +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) := by
  set κ : ℝ≥0∞ := (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹ * ((Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹ *
    (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹) with hκ
  have hid0 : Hidden (Ω := (Tw → Msg) × ((Tw → Y) × (Tw × Msg → Y))) (fun _ ↦ κ)
      (fun ω ↦ ω.2) (fun ω ↦ udgMarked c ω.1) (Fintype.card Msg : ℝ≥0∞)⁻¹ :=
    hidden_indep κ _ _ fun p ↦ by
      refine le_trans (Finset.sum_le_sum fun xs _ ↦ ?_) (le_of_eq (sum_udMarked p))
      by_cases hp : p ∈ udgMarked c xs
      · have : p ∈ udMarked xs := by
          simp only [udgMarked, udMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact hp.2
        simp [hp, this]
      · simp [hp]
  have hid := (hid0.reweight (fun v ↦ w (o (yvals c v.1) v.2))).map_emb e
  have hw : ∑ ω : (Tw → Msg) × ((Tw → Y) × (Tw × Msg → Y)),
      κ * w (o (yvals c ω.2.1) ω.2.2) ≤ 1 :=
    le_trans (le_of_eq (ud_coupling_ideal (fun ys R ↦ w (o (yvals c ys) R)))) hW
  have hS : ∀ (ω : (Tw → Msg) × ((Tw → Y) × (Tw × Msg → Y))) (z : Z),
      patch F e (udRep c ω.1 ω.2.1 ω.2.2) z ≠ patch F e ω.2.2 z →
        z ∈ (udgMarked c ω.1).map e := by
    intro ω z h
    by_cases hz : ∃ p, e p = z
    · obtain ⟨p, rfl⟩ := hz
      rw [patch_apply, patch_apply] at h
      rw [Finset.mem_map']
      simp only [udgMarked, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hne
      exact h (by simp [udRep, hne])
    · exact (h (by rw [patch_of_not_range _ _ _ _ hz, patch_of_not_range _ _ _ _ hz])).elim
  have hr := ud_coupling_real c o h1
    (fun a H ↦ w a * (M a).prob (patch F e H) (E a))
  have hi := ud_coupling_ideal (Msg := Msg)
    (fun ys R ↦ w (o (yvals c ys) R) *
      (M (o (yvals c ys) R)).prob (patch F e R) (E (o (yvals c ys) R)))
  rw [← hr, ← hi]
  constructor
  · have hs := hid.real_le_hyb_add hw (fun v ↦ M (o (yvals c v.1) v.2))
      (fun ω ↦ patch F e (udRep c ω.1 ω.2.1 ω.2.2)) (fun v ↦ patch F e v.2) hS
      (fun v ↦ E (o (yvals c v.1) v.2))
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ω _ ↦ ?_))
      (le_trans hs (add_le_add (le_of_eq (Finset.sum_congr rfl fun ω _ ↦ ?_)) le_rfl))
    · exact (mul_assoc _ _ _).symm
    · exact mul_assoc _ _ _
  · have hs := hid.hyb_le_real_add hw (fun v ↦ M (o (yvals c v.1) v.2))
      (fun ω ↦ patch F e (udRep c ω.1 ω.2.1 ω.2.2)) (fun v ↦ patch F e v.2) hS
      (fun v ↦ E (o (yvals c v.1) v.2))
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ω _ ↦ ?_))
      (le_trans hs (add_le_add (le_of_eq (Finset.sum_congr rfl fun ω _ ↦ ?_)) le_rfl))
    · exact (mul_assoc _ _ _).symm
    · exact mul_assoc _ _ _

/-- Weighted probability of the real world. -/
noncomputable def udEmbReal : ℝ≥0∞ :=
  ∑ R : Tw × Msg → Y, ∑ xs : Tw → Msg,
    ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Msg) : ℝ≥0∞)⁻¹) *
      (w (o (tvals c R xs) R) *
        (M (o (tvals c R xs) R)).prob (patch F e R) (E (o (tvals c R xs) R)))

/-- Weighted probability of the ideal world. -/
noncomputable def udEmbIdeal : ℝ≥0∞ :=
  ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
    ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
      (w (o (yvals c ys) R) *
        (M (o (yvals c ys) R)).prob (patch F e R) (E (o (yvals c ys) R)))

/-- Average weight (ideal world; equal to that of the real world, `ud_embedded_weight_eq`). -/
noncomputable def udEmbWeight : ℝ≥0∞ :=
  ∑ R : Tw × Msg → Y, ∑ ys : Tw → Y,
    ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card (Tw → Y) : ℝ≥0∞)⁻¹) *
      w (o (yvals c ys) R)

theorem udEmbReal_smul (s : ℝ≥0∞) :
    udEmbReal e F c o M E (fun a ↦ s * w a) = s * udEmbReal e F c o M E w := by
  unfold udEmbReal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun xs _ ↦ by ring

theorem udEmbIdeal_smul (s : ℝ≥0∞) :
    udEmbIdeal e F c o M E (fun a ↦ s * w a) = s * udEmbIdeal e F c o M E w := by
  unfold udEmbIdeal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ys _ ↦ by ring

theorem udEmbWeight_smul (s : ℝ≥0∞) :
    udEmbWeight (Msg := Msg) c o (fun a ↦ s * w a) = s * udEmbWeight (Msg := Msg) c o w := by
  unfold udEmbWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ys _ ↦ by ring

theorem udEmbIdeal_le_weight [Nonempty Z] :
    udEmbIdeal e F c o M E w ≤ udEmbWeight (Msg := Msg) c o w := by
  unfold udEmbIdeal udEmbWeight
  gcongr with R _ ys _
  calc w (o (yvals c ys) R) * (M (o (yvals c ys) R)).prob (patch F e R) (E (o (yvals c ys) R))
      ≤ w (o (yvals c ys) R) * 1 := by
        gcongr
        exact (M _).prob_le_one _ _
    _ = _ := mul_one _

include h1 in
theorem udEmbReal_le_weight [Nonempty Z] [Nonempty Msg] :
    udEmbReal e F c o M E w ≤ udEmbWeight (Msg := Msg) c o w := by
  unfold udEmbReal udEmbWeight
  rw [← ud_embedded_weight_eq c o h1 w]
  gcongr with R _ xs _
  calc w (o (tvals c R xs) R) * (M (o (tvals c R xs) R)).prob (patch F e R) (E (o (tvals c R xs) R))
      ≤ w (o (tvals c R xs) R) * 1 := by
        gcongr
        exact (M _).prob_le_one _ _
    _ = _ := mul_one _

include h1 in
/-- Both directions, error proportional to the average weight. -/
theorem ud_embedded_both [Nonempty Z] [Nonempty Msg] (hwfin : ∀ a, w a ≠ ⊤) :
    (udEmbReal e F c o M E w ≤ udEmbIdeal e F c o M E w +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) * udEmbWeight (Msg := Msg) c o w) ∧
    (udEmbIdeal e F c o M E w ≤ udEmbReal e F c o M E w +
        4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) * udEmbWeight (Msg := Msg) c o w) := by
  set W : ℝ≥0∞ := udEmbWeight (Msg := Msg) c o w with hWdef
  set δ : ℝ≥0∞ := 4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) with hδ
  have hR := udEmbReal_le_weight e F c o h1 M E w
  have hI := udEmbIdeal_le_weight (Msg := Msg) e F c o M E w
  by_cases h0 : W = 0
  · rw [← hWdef, h0] at hR hI
    exact ⟨hR.trans zero_le, hI.trans zero_le⟩
  have htop : W ≠ ⊤ := by
    rw [hWdef]
    unfold udEmbWeight
    refine ENNReal.sum_ne_top.2 fun R _ ↦ ENNReal.sum_ne_top.2 fun ys _ ↦ ?_
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) (hwfin _)
    · exact ENNReal.inv_ne_top.2 (by exact_mod_cast Fintype.card_ne_zero)
    · exact ENNReal.inv_ne_top.2 (by exact_mod_cast Fintype.card_ne_zero)
  have iW : W * W⁻¹ = 1 := ENNReal.mul_inv_cancel h0 htop
  have hn := ud_embedded_normalised e F c o h1 M E (fun a ↦ W⁻¹ * w a) (by
    have := udEmbWeight_smul (Msg := Msg) c o w W⁻¹
    unfold udEmbWeight at this
    rw [this]
    exact le_of_eq (by rw [mul_comm]; exact iW))
  have hn1 : W⁻¹ * udEmbReal e F c o M E w ≤ W⁻¹ * udEmbIdeal e F c o M E w + δ := by
    rw [← udEmbReal_smul, ← udEmbIdeal_smul]
    exact hn.1
  have hn2 : W⁻¹ * udEmbIdeal e F c o M E w ≤ W⁻¹ * udEmbReal e F c o M E w + δ := by
    rw [← udEmbReal_smul, ← udEmbIdeal_smul]
    exact hn.2
  have key : ∀ P Q : ℝ≥0∞, W⁻¹ * P ≤ W⁻¹ * Q + δ → P ≤ Q + δ * W := by
    intro P Q h
    calc P = W * (W⁻¹ * P) := by rw [← mul_assoc, iW, one_mul]
      _ ≤ W * (W⁻¹ * Q + δ) := mul_le_mul' le_rfl h
      _ = (W * W⁻¹) * Q + δ * W := by ring
      _ = Q + δ * W := by rw [iW, one_mul]
  exact ⟨key _ _ hn1, key _ _ hn2⟩

include h1 in
/-- **UD on an embedded row, real ≤ ideal.**  The weighted probability of the event in the real
world is at most that in the ideal world plus `4 q / √|Msg|` times the average weight.  (The
weights must be finite.) -/
theorem ud_embedded_real_le_ideal_add [Nonempty Z] [Nonempty Msg] (hwfin : ∀ a, w a ≠ ⊤) :
    udEmbReal e F c o M E w ≤ udEmbIdeal e F c o M E w +
      4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) * udEmbWeight (Msg := Msg) c o w :=
  (ud_embedded_both e F c o h1 M E w hwfin).1

include h1 in
/-- **UD on an embedded row, ideal ≤ real.** -/
theorem ud_embedded_ideal_le_real_add [Nonempty Z] [Nonempty Msg] (hwfin : ∀ a, w a ≠ ⊤) :
    udEmbIdeal e F c o M E w ≤ udEmbReal e F c o M E w +
      4 * q * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) * udEmbWeight (Msg := Msg) c o w :=
  (ud_embedded_both e F c o h1 M E w hwfin).2

end Core

end

end PQ.QROM

#print axioms PQ.QROM.ud_embedded_normalised
#print axioms PQ.QROM.ud_embedded_weight_eq
#print axioms PQ.QROM.ud_embedded_real_le_ideal_add
#print axioms PQ.QROM.ud_embedded_ideal_le_real_add
