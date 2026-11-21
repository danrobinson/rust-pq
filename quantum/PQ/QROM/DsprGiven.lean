import PQ.QROM.SprGiven
import PQ.QROM.Distinguish

/-!
# Decisional second-preimage resistance on an embedded random row: multi-target, weighted

Embedded-row setting of `spr_embedded_obs_weighted_le`: the oracle is `patch F e R` (`F` fixed,
`R : Tw × Msg → Y` uniform on the range of `e : Tw × Msg ↪ Z`); `c : Tw → Option Msg` is a fixed
partial target assignment (at most one target per tweak); the algorithm, its decodings and a
weight depend on an observation `o R` of the row that does not depend on the non-target points of
the tweaks that have a target (`hobs`: the target values and the rows without a target may be
observed).

The algorithm outputs a leaf `l`, decoded to a validity flag `V`, a tweak `tw` (with a target
whenever `V` holds, `hV`) and a bit `b`.

* success: `V` and the bit equals the truth value of `rowSP c R tw` ("the target of the tweak
  has a second preimage in its row");
* baseline (`SPprob`): `V` and `rowSP c R tw`, whatever the bit.

`dspr_embedded_weighted_le`: for ADDITIVE models (`HybridModel.Additive`: the probability of a
disjoint union of events is the sum; the fields of `HybridModel` do not imply it),

`success ≤ baseline + ((γ − (1 − γ)) + 8 q / √|Y|) · (average weight)`,
`γ = (1 − 1/|Y|)^(|Msg| − 1)` the probability that a target has no second preimage in its row.

Proof: the coupling of `mt_spr_fixed_le` / `hidden_sg_obs` (targets kept, every other point of a
target row resampled away from the target value).  Real and hybrid worlds are `4 q / √|Y|`-close
for each of the two (world-dependent) events.  In the hybrid world the indicator "no second
preimage in the row of `t`" is independent of the view and has probability `γ`
(`dspr_row_indep`), and by additivity both probabilities split over the chosen tweak and the bit.
-/

open ENNReal Finset

set_option linter.unusedSectionVars false

namespace PQ.QROM

/-! ### Coordinatewise weights with a prescribed push-forward -/

section Coupling

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- `sum_marked_dep` for a general coordinate weight `a y` whose push-forward under
`resample y` is the constant `β`. -/
theorem sum_weight_dep (k : X) (a : Y → Y × NZ Y → ℝ≥0∞) (β : ℝ≥0∞)
    (h : ∀ y z, ∑ t : Y × NZ Y with resample y t = z, a y t =
      ∑ t : Y × NZ Y with resample y t = z, β)
    (u : (X → Y × NZ Y) → Y) (hu : ∀ τ t, u (Function.update τ k t) = u τ)
    (Φ : Y → (X → Y × NZ Y) → ℝ≥0∞) (hΦ : ∀ z τ t, Φ z (Function.update τ k t) = Φ z τ) :
    ∑ τ : X → Y × NZ Y, a (u τ) (τ k) * Φ (resample (u τ) (τ k)) τ =
      β * ∑ τ : X → Y × NZ Y, Φ (resample (u τ) (τ k)) τ := by
  have hL : ∀ τ : X → Y × NZ Y, a (u τ) (τ k) * Φ (resample (u τ) (τ k)) τ =
      ∑ y : Y, a y (τ k) * ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) := by
    intro τ
    rw [Finset.sum_eq_single (u τ)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : ∀ τ : X → Y × NZ Y, β * Φ (resample (u τ) (τ k)) τ =
      ∑ y : Y, β * ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) := by
    intro τ
    rw [Finset.sum_eq_single (u τ)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∑ τ : X → Y × NZ Y, a (u τ) (τ k) * Φ (resample (u τ) (τ k)) τ
      = ∑ y : Y, ∑ τ : X → Y × NZ Y, a y (τ k) *
          ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) :=
        (Finset.sum_congr rfl fun τ _ ↦ hL τ).trans Finset.sum_comm
    _ = ∑ y : Y, ∑ τ : X → Y × NZ Y, β *
          ((if u τ = y then (1 : ℝ≥0∞) else 0) * Φ (resample y (τ k)) τ) :=
        Finset.sum_congr rfl fun y _ ↦
          sum_coord_change k (resample y) (resample y) (a y) (fun _ ↦ β) (h y)
            (fun z τ ↦ (if u τ = y then (1 : ℝ≥0∞) else 0) * Φ z τ)
            (by intro z τ t; rw [hu, hΦ])
    _ = ∑ τ : X → Y × NZ Y, β * Φ (resample (u τ) (τ k)) τ :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun τ _ ↦ (hR τ).symm)
    _ = _ := by rw [Finset.mul_sum]

/-- `sum_marked_view` for a general coordinate weight. -/
theorem sum_weight_view (k : X) (a : Y → Y × NZ Y → ℝ≥0∞) (β : ℝ≥0∞)
    (h : ∀ y z, ∑ t : Y × NZ Y with resample y t = z, a y t =
      ∑ t : Y × NZ Y with resample y t = z, β)
    (u : (X → Y × NZ Y) → Y) (hu : ∀ τ t, u (Function.update τ k t) = u τ)
    (G : (X → Y × NZ Y) → X → Y) (hGk : ∀ τ, G τ k = resample (u τ) (τ k))
    (hG : ∀ τ t j, j ≠ k → G (Function.update τ k t) j = G τ j)
    (Ψ : (X → Y × NZ Y) → (X → Y) → ℝ≥0∞)
    (hΨ : ∀ τ t g, Ψ (Function.update τ k t) g = Ψ τ g) :
    ∑ τ : X → Y × NZ Y, a (u τ) (τ k) * Ψ τ (G τ) = β * ∑ τ : X → Y × NZ Y, Ψ τ (G τ) := by
  have e := sum_weight_dep k a β h u hu (fun z τ ↦ Ψ τ (Function.update (G τ) k z)) (by
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

/-- **Independence of the unmarked indicators.**  For a set `s` of coordinates that are resampled
away from the target value `u τ`: given the hybrid function, all points of `s` are unmarked with
probability `(1 - 1/|Y|)^|s|`. -/
theorem sum_unmarked_prod (s : Finset X) (u : (X → Y × NZ Y) → Y)
    (hu : ∀ k ∈ s, ∀ τ t, u (Function.update τ k t) = u τ)
    (G : (X → Y × NZ Y) → X → Y) (hGk : ∀ k ∈ s, ∀ τ, G τ k = resample (u τ) (τ k))
    (hG : ∀ k ∈ s, ∀ τ t j, j ≠ k → G (Function.update τ k t) j = G τ j)
    (Ψ : (X → Y × NZ Y) → (X → Y) → ℝ≥0∞)
    (hΨ : ∀ k ∈ s, ∀ τ t g, Ψ (Function.update τ k t) g = Ψ τ g) :
    ∑ τ : X → Y × NZ Y,
        (∏ k ∈ s, if (τ k).1 ≠ u τ then (1 : ℝ≥0∞) else 0) * Ψ τ (G τ) =
      (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ #s * ∑ τ : X → Y × NZ Y, Ψ τ (G τ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hks : k ∈ insert k s := Finset.mem_insert_self k s
    have e := sum_weight_view k (fun y t ↦ if t.1 ≠ y then (1 : ℝ≥0∞) else 0)
      (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) resample_fiber_ne u (hu k hks) G (hGk k hks) (hG k hks)
      (fun τ g ↦ (∏ k' ∈ s, if (τ k').1 ≠ u τ then (1 : ℝ≥0∞) else 0) * Ψ τ g) (by
        intro τ t g
        rw [hΨ k hks]
        congr 1
        refine Finset.prod_congr rfl fun k' hk' ↦ ?_
        have hne : k' ≠ k := fun h ↦ hk (h ▸ hk')
        rw [Function.update_of_ne hne, hu k hks])
    calc ∑ τ : X → Y × NZ Y,
          (∏ k' ∈ insert k s, if (τ k').1 ≠ u τ then (1 : ℝ≥0∞) else 0) * Ψ τ (G τ)
        = ∑ τ : X → Y × NZ Y, (if (τ k).1 ≠ u τ then (1 : ℝ≥0∞) else 0) *
            ((∏ k' ∈ s, if (τ k').1 ≠ u τ then (1 : ℝ≥0∞) else 0) * Ψ τ (G τ)) :=
          Finset.sum_congr rfl fun τ _ ↦ by rw [Finset.prod_insert hk, mul_assoc]
      _ = (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) * ∑ τ : X → Y × NZ Y,
            (∏ k' ∈ s, if (τ k').1 ≠ u τ then (1 : ℝ≥0∞) else 0) * Ψ τ (G τ) := e
      _ = (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) * ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ #s *
            ∑ τ : X → Y × NZ Y, Ψ τ (G τ)) := by
          rw [ih (fun k' hk' ↦ hu k' (Finset.mem_insert_of_mem hk'))
            (fun k' hk' ↦ hGk k' (Finset.mem_insert_of_mem hk'))
            (fun k' hk' ↦ hG k' (Finset.mem_insert_of_mem hk'))
            (fun k' hk' ↦ hΨ k' (Finset.mem_insert_of_mem hk'))]
      _ = _ := by rw [Finset.card_insert_of_notMem hk, pow_succ]; ring

end Coupling

/-! ### Additive models -/

section Additive

variable {X Y Leaf : Type} [Fintype X] [DecidableEq Y] {q : ℕ}

/-- The probability of a disjoint union of two events is the sum of their probabilities.  (Not a
consequence of the fields of `HybridModel`; it holds for the models of quantum query programs.) -/
def HybridModel.Additive (m : HybridModel X Y Leaf q) : Prop :=
  ∀ (H : X → Y) (E E' : Leaf → Prop), (∀ l, ¬ (E l ∧ E' l)) →
    m.prob H (fun l ↦ E l ∨ E' l) = m.prob H E + m.prob H E'

theorem HybridModel.Additive.prob_false [Nonempty X] {m : HybridModel X Y Leaf q}
    (hm : m.Additive) (H : X → Y) : m.prob H (fun _ ↦ False) = 0 := by
  have h := hm H (fun _ ↦ False) (fun _ ↦ False) (by simp)
  simp only [or_self] at h
  have hfin : m.prob H (fun _ ↦ False) ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (m.prob_le_one _ _)
  have h' : m.prob H (fun _ ↦ False) + 0 = m.prob H (fun _ ↦ False) + m.prob H (fun _ ↦ False) := by
    rw [add_zero]; exact h
  exact ((ENNReal.add_right_inj hfin).1 h').symm

theorem HybridModel.Additive.prob_exists [Nonempty X] {m : HybridModel X Y Leaf q}
    (hm : m.Additive) (H : X → Y) {ι : Type} (s : Finset ι) (Ev : ι → Leaf → Prop)
    (hdisj : ∀ i j, i ≠ j → ∀ l, ¬ (Ev i l ∧ Ev j l)) :
    m.prob H (fun l ↦ ∃ i ∈ s, Ev i l) = ∑ i ∈ s, m.prob H (Ev i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, false_and, exists_false, Finset.sum_empty]
    exact hm.prob_false H
  | insert i s hi ih =>
    have hev : (fun l ↦ ∃ j ∈ insert i s, Ev j l) = fun l ↦ Ev i l ∨ ∃ j ∈ s, Ev j l := by
      funext l
      simp
    rw [hev, hm H _ _ (by
      rintro l ⟨h1, j, hj, h2⟩
      exact hdisj i j (fun h ↦ hi (h ▸ hj)) l ⟨h1, h2⟩), ih, Finset.sum_insert hi]

end Additive

/-! ### Splitting over the chosen tweak and the bit -/

section Split

variable {X Y Leaf Tw : Type} [Fintype X] [DecidableEq Y] {q : ℕ} [Fintype Tw]

open Classical in
/-- Success splits over the chosen tweak: on a tweak with a second preimage the bit must be set,
otherwise it must not. -/
theorem dspr_prob_succ [Nonempty X] {m : HybridModel X Y Leaf q} (hm : m.Additive) (H : X → Y)
    (Vl : Leaf → Prop) (twl : Leaf → Tw) (bl : Leaf → Prop) (sp : Tw → Prop) :
    m.prob H (fun l ↦ Vl l ∧ (sp (twl l) ↔ bl l)) =
      ∑ t : Tw, (if sp t then m.prob H (fun l ↦ Vl l ∧ twl l = t ∧ bl l)
        else m.prob H (fun l ↦ Vl l ∧ twl l = t ∧ ¬ bl l)) := by
  have hev : (fun l ↦ Vl l ∧ (sp (twl l) ↔ bl l)) =
      fun l ↦ ∃ t ∈ (univ : Finset Tw), Vl l ∧ twl l = t ∧ (sp t ↔ bl l) := by
    funext l
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨twl l, Finset.mem_univ _, h1, rfl, h2⟩
    · rintro ⟨t, -, h1, rfl, h2⟩
      exact ⟨h1, h2⟩
  rw [hev, hm.prob_exists H univ _ (by
    rintro i j hij l ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩
    exact hij (h1.symm.trans h2))]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases ht : sp t
  · simp only [ht, ite_true, true_iff]
  · simp only [ht, ite_false, false_iff]

open Classical in
/-- The baseline splits over the chosen tweak. -/
theorem dspr_prob_sp [Nonempty X] {m : HybridModel X Y Leaf q} (hm : m.Additive) (H : X → Y)
    (Vl : Leaf → Prop) (twl : Leaf → Tw) (bl : Leaf → Prop) (sp : Tw → Prop) :
    m.prob H (fun l ↦ Vl l ∧ sp (twl l)) =
      ∑ t : Tw, (if sp t then m.prob H (fun l ↦ Vl l ∧ twl l = t ∧ bl l) +
        m.prob H (fun l ↦ Vl l ∧ twl l = t ∧ ¬ bl l) else 0) := by
  have hev : (fun l ↦ Vl l ∧ sp (twl l)) =
      fun l ↦ ∃ t ∈ (univ : Finset Tw), Vl l ∧ twl l = t ∧ sp t := by
    funext l
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨twl l, Finset.mem_univ _, h1, rfl, h2⟩
    · rintro ⟨t, -, h1, rfl, h2⟩
      exact ⟨h1, h2⟩
  rw [hev, hm.prob_exists H univ _ (by
    rintro i j hij l ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩
    exact hij (h1.symm.trans h2))]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases ht : sp t
  · simp only [ht, ite_true, and_true]
    have hsplit : (fun l ↦ Vl l ∧ twl l = t) =
        fun l ↦ (Vl l ∧ twl l = t ∧ bl l) ∨ (Vl l ∧ twl l = t ∧ ¬ bl l) := by
      funext l
      apply propext
      by_cases hb : bl l <;> simp [hb]
    rw [hsplit]
    exact hm H _ _ (by
      rintro l ⟨⟨-, -, h1⟩, ⟨-, -, h2⟩⟩
      exact h2 h1)
  · simp only [ht, ite_false, and_false]
    exact hm.prob_false H

/-- The pieces over the chosen tweak have total probability at most one. -/
theorem dspr_sum_piece_le [Nonempty X] {m : HybridModel X Y Leaf q} (hm : m.Additive) (H : X → Y)
    (Vl : Leaf → Prop) (twl : Leaf → Tw) (Bl : Leaf → Prop) :
    ∑ t : Tw, m.prob H (fun l ↦ Vl l ∧ twl l = t ∧ Bl l) ≤ 1 := by
  rw [← hm.prob_exists H univ (fun t l ↦ Vl l ∧ twl l = t ∧ Bl l) (by
    rintro i j hij l ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩
    exact hij (h1.symm.trans h2))]
  exact m.prob_le_one _ _

end Split

/-! ### The embedded DSPR lemma -/

section Dspr

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The target of the tweak `t` has a second preimage in its row. -/
def rowSP (c : Tw → Option Msg) (R : Tw × Msg → Y) (t : Tw) : Prop :=
  ∃ m, c t = some m ∧ ∃ m', m' ≠ m ∧ R (t, m') = R (t, m)

/-- Indicator that the target of the tweak `t` (if any) has no second preimage in its row. -/
noncomputable def nspw (c : Tw → Option Msg) (R : Tw × Msg → Y) (t : Tw) : ℝ≥0∞ :=
  (c t).elim 1 fun m ↦ ∏ m' ∈ univ.erase m, if R (t, m') ≠ R (t, m) then 1 else 0

theorem nspw_of_SP {c : Tw → Option Msg} {R : Tw × Msg → Y} {t : Tw} (h : rowSP c R t) :
    nspw c R t = 0 := by
  obtain ⟨m, hc, m', hne, heq⟩ := h
  simp only [nspw, hc, Option.elim_some]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) (by simp [heq])

theorem nspw_of_not_SP {c : Tw → Option Msg} {R : Tw × Msg → Y} {t : Tw} (h : ¬ rowSP c R t) :
    nspw c R t = 1 := by
  cases hc : c t with
  | none => simp [nspw, hc]
  | some m =>
    simp only [nspw, hc, Option.elim_some]
    refine Finset.prod_eq_one fun m' hm' ↦ ?_
    have : R (t, m') ≠ R (t, m) := fun e ↦ h ⟨m, hc, m', (Finset.mem_erase.1 hm').1, e⟩
    simp [this]

/-- **Independence of "no second preimage" from the view.**  In the coupling of `hidden_sg_obs`,
for a tweak `t` with target `m`: given the observation and the hybrid function, the target has no
second preimage in its row with probability `(1 - 1/|Y|)^(|Msg| - 1)`. -/
theorem dspr_row_indep {A : Type} (c : Tw → Option Msg) (o : (Tw × Msg → Y) → A)
    (hobs : ∀ (k : Tw × Msg) (m : Msg), c k.1 = some m → k.2 ≠ m →
      ∀ (R : Tw × Msg → Y) (v : Y), o (Function.update R k v) = o R)
    (t : Tw) (m : Msg) (hc : c t = some m) (Ψ : A → (Tw × Msg → Y) → ℝ≥0∞) :
    ∑ τ : Tw × Msg → Y × NZ Y,
        nspw c (fun k ↦ (τ k).1) t * Ψ (o (fun k ↦ (τ k).1)) (sgG c τ) =
      (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) *
        ∑ τ : Tw × Msg → Y × NZ Y, Ψ (o (fun k ↦ (τ k).1)) (sgG c τ) := by
  let s : Finset (Tw × Msg) := (univ.erase m).map
    ⟨fun m' ↦ (t, m'), fun _ _ h ↦ (Prod.ext_iff.1 h).2⟩
  have hs : ∀ k ∈ s, k.1 = t ∧ k.2 ≠ m := by
    intro k hk
    obtain ⟨m', hm', rfl⟩ := Finset.mem_map.1 hk
    exact ⟨rfl, (Finset.mem_erase.1 hm').1⟩
  have hcard : #s = Fintype.card Msg - 1 := by
    rw [Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ]
  have hn : ∀ τ : Tw × Msg → Y × NZ Y, nspw c (fun k ↦ (τ k).1) t =
      ∏ k ∈ s, if (τ k).1 ≠ (τ (t, m)).1 then (1 : ℝ≥0∞) else 0 := by
    intro τ
    rw [show nspw c (fun k ↦ (τ k).1) t = ∏ m' ∈ univ.erase m,
      (if (τ (t, m')).1 ≠ (τ (t, m)).1 then (1 : ℝ≥0∞) else 0) by
        simp only [nspw, hc, Option.elim_some]]
    exact (Finset.prod_map (univ.erase m)
      (⟨fun m' ↦ (t, m'), fun _ _ h ↦ (Prod.ext_iff.1 h).2⟩ : Msg ↪ Tw × Msg)
      (fun k ↦ if (τ k).1 ≠ (τ (t, m)).1 then (1 : ℝ≥0∞) else 0)).symm
  have hne : ∀ k ∈ s, ∀ t' m', c t' = some m' → (t', m') ≠ k := by
    intro k hk t' m' h heq
    obtain ⟨h1, h2⟩ := hs k hk
    have e1 : k.1 = t' := by rw [← heq]
    have e2 : k.2 = m' := by rw [← heq]
    rw [← e1, h1, hc] at h
    exact h2 (e2.trans (Option.some.inj h).symm)
  have e := sum_unmarked_prod s (fun τ : Tw × Msg → Y × NZ Y ↦ (τ (t, m)).1)
    (fun k hk τ v ↦ by simp [Function.update_of_ne (hne k hk t m hc)])
    (sgG c)
    (fun k hk τ ↦ by
      obtain ⟨h1, h2⟩ := hs k hk
      have hck : c k.1 = some m := by rw [h1]; exact hc
      have : (k.1, m) = (t, m) := by rw [h1]
      simp [sgG, hck, h2, this])
    (fun k hk τ v j hj ↦ by
      cases hcj : c j.1 with
      | none => simp [sgG, hcj, Function.update_of_ne hj]
      | some m' =>
        simp [sgG, hcj, Function.update_of_ne hj, Function.update_of_ne (hne k hk j.1 m' hcj)])
    (fun τ g ↦ Ψ (o (fun k ↦ (τ k).1)) g)
    (fun k hk τ v g ↦ by
      obtain ⟨h1, h2⟩ := hs k hk
      have hck : c k.1 = some m := by rw [h1]; exact hc
      have : (fun j ↦ (Function.update τ k v j).1) =
          Function.update (fun j ↦ (τ j).1) k v.1 := by
        funext j
        by_cases hj : j = k
        · rw [hj]; simp
        · simp [Function.update_of_ne hj]
      rw [this, hobs k m hck h2])
  rw [hcard] at e
  rw [← e]
  exact Finset.sum_congr rfl fun τ _ ↦ by rw [hn]

end Dspr

/-! ### The main lemma -/

section Main

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Leaf : Type} {q : ℕ} {A : Type}
  (e : Tw × Msg ↪ Z) (F : Z → Y) (c : Tw → Option Msg) (o : (Tw × Msg → Y) → A)
  (hobs : ∀ (k : Tw × Msg) (m : Msg), c k.1 = some m → k.2 ≠ m →
    ∀ (R : Tw × Msg → Y) (v : Y), o (Function.update R k v) = o R)
  (M : A → HybridModel Z Y Leaf q) (hadd : ∀ a, (M a).Additive)
  (V : A → Leaf → Prop) (tw : A → Leaf → Tw) (b : A → Leaf → Prop)
  (hV : ∀ a l, V a l → ∃ m, c (tw a l) = some m) (w : A → ℝ≥0∞)

/-- The success event: valid, and the bit predicts whether the chosen target has a second
preimage. -/
def dsprEvS (R : Tw × Msg → Y) : Leaf → Prop :=
  fun l ↦ V (o R) l ∧ (rowSP c R (tw (o R) l) ↔ b (o R) l)

/-- The baseline event: valid, and the chosen target has a second preimage. -/
def dsprEvP (R : Tw × Msg → Y) : Leaf → Prop :=
  fun l ↦ V (o R) l ∧ rowSP c R (tw (o R) l)

/-- Weighted success probability. -/
noncomputable def dsprEmbSucc : ℝ≥0∞ :=
  ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ *
    (w (o R) * (M (o R)).prob (patch F e R) (dsprEvS c o V tw b R))

/-- Weighted baseline probability. -/
noncomputable def dsprEmbSP : ℝ≥0∞ :=
  ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ *
    (w (o R) * (M (o R)).prob (patch F e R) (dsprEvP c o V tw R))

/-- Average weight. -/
noncomputable def dsprEmbWeight : ℝ≥0∞ :=
  ∑ R : Tw × Msg → Y, (Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * w (o R)

/-- The probability, against the function `g`, of: valid, chosen tweak `t`, and `B`. -/
noncomputable def dsprPiece (B : A → Leaf → Prop) (t : Tw) (a : A) (g : Tw × Msg → Y) : ℝ≥0∞ :=
  (M a).prob (patch F e g) (fun l ↦ V a l ∧ tw a l = t ∧ B a l)

include hobs hadd hV in
open Classical in
/-- **The hybrid world.**  Against the hybrid function, success exceeds the baseline by at most
`max 0 (2γ − 1)`. -/
theorem dspr_hybrid_le [Nonempty Z] (κ : ℝ≥0∞)
    (hw : ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) ≤ 1) :
    ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
        (M (o (fun k ↦ (τ k).1))).prob (patch F e (sgG c τ))
          (dsprEvS c o V tw b (fun k ↦ (τ k).1)) ≤
      ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
        (M (o (fun k ↦ (τ k).1))).prob (patch F e (sgG c τ))
          (dsprEvP c o V tw (fun k ↦ (τ k).1)) +
        ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) -
          (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1))) := by
  set γ : ℝ≥0∞ := (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) with hγdef
  have hγ : γ ≤ 1 := pow_le_one₀ zero_le tsub_le_self
  -- abbreviations
  set S : ℝ≥0∞ := ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
    (M (o (fun k ↦ (τ k).1))).prob (patch F e (sgG c τ))
      (dsprEvS c o V tw b (fun k ↦ (τ k).1)) with hS
  set Q : ℝ≥0∞ := ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
    (M (o (fun k ↦ (τ k).1))).prob (patch F e (sgG c τ))
      (dsprEvP c o V tw (fun k ↦ (τ k).1)) with hQ
  let nb : A → Leaf → Prop := fun a l ↦ ¬ b a l
  set P1 : ℝ≥0∞ := ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
    dsprPiece e F M V tw b t (o (fun k ↦ (τ k).1)) (sgG c τ) with hP1
  set P0 : ℝ≥0∞ := ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
    dsprPiece e F M V tw nb t (o (fun k ↦ (τ k).1)) (sgG c τ) with hP0
  -- pieces on tweaks without a target vanish
  have hzero : ∀ (B : A → Leaf → Prop) (t : Tw), c t = none →
      ∀ (a : A) (g : Tw × Msg → Y), dsprPiece e F M V tw B t a g = 0 := by
    intro B t hc a g
    have hev : (fun l ↦ V a l ∧ tw a l = t ∧ B a l) = fun _ ↦ False := by
      funext l
      apply propext
      refine ⟨fun h ↦ ?_, False.elim⟩
      obtain ⟨m, hm⟩ := hV a l h.1
      rw [h.2.1, hc] at hm
      cases hm
    unfold dsprPiece
    rw [hev]
    exact (hadd a).prob_false _
  -- independence
  have hindep : ∀ B : A → Leaf → Prop,
      ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
        (nspw c (fun k ↦ (τ k).1) t *
          dsprPiece e F M V tw B t (o (fun k ↦ (τ k).1)) (sgG c τ)) =
      γ * ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
        dsprPiece e F M V tw B t (o (fun k ↦ (τ k).1)) (sgG c τ) := by
    intro B
    calc _ = ∑ t : Tw, ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
          (nspw c (fun k ↦ (τ k).1) t *
            dsprPiece e F M V tw B t (o (fun k ↦ (τ k).1)) (sgG c τ)) := Finset.sum_comm
      _ = ∑ t : Tw, γ * ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
            dsprPiece e F M V tw B t (o (fun k ↦ (τ k).1)) (sgG c τ) := by
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          cases hc : c t with
          | none => simp [hzero B t hc]
          | some m =>
            have e1 := dspr_row_indep c o hobs t m hc
              (fun a g ↦ κ * w a * dsprPiece e F M V tw B t a g)
            refine Eq.trans (Finset.sum_congr rfl fun τ _ ↦ ?_) e1
            ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  -- total mass of the pieces
  have hpiece : ∀ B : A → Leaf → Prop,
      ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
        dsprPiece e F M V tw B t (o (fun k ↦ (τ k).1)) (sgG c τ) ≤ 1 := by
    intro B
    refine le_trans (Finset.sum_le_sum fun τ _ ↦ ?_) hw
    rw [← Finset.mul_sum]
    calc κ * w (o (fun k ↦ (τ k).1)) *
          ∑ t : Tw, dsprPiece e F M V tw B t (o (fun k ↦ (τ k).1)) (sgG c τ)
        ≤ κ * w (o (fun k ↦ (τ k).1)) * 1 :=
          mul_le_mul' le_rfl (dspr_sum_piece_le (hadd _) _ _ _ _)
      _ = _ := mul_one _
  have hP1le : P1 ≤ 1 := hpiece b
  have hP0le : P0 ≤ 1 := hpiece nb
  -- decomposition of the two experiments
  have hSd : S = ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
      (if rowSP c (fun k ↦ (τ k).1) t
        then dsprPiece e F M V tw b t (o (fun k ↦ (τ k).1)) (sgG c τ)
        else dsprPiece e F M V tw nb t (o (fun k ↦ (τ k).1)) (sgG c τ)) := by
    rw [hS]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [← Finset.mul_sum]
    congr 1
    exact dspr_prob_succ (hadd _) _ _ _ _ _
  have hQd : Q = ∑ τ : Tw × Msg → Y × NZ Y, ∑ t : Tw, κ * w (o (fun k ↦ (τ k).1)) *
      (if rowSP c (fun k ↦ (τ k).1) t
        then dsprPiece e F M V tw b t (o (fun k ↦ (τ k).1)) (sgG c τ) +
          dsprPiece e F M V tw nb t (o (fun k ↦ (τ k).1)) (sgG c τ)
        else 0) := by
    rw [hQ]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [← Finset.mul_sum]
    congr 1
    exact dspr_prob_sp (hadd _) _ _ _ (b (o (fun k ↦ (τ k).1))) _
  have hA : S + γ * P1 = P1 + γ * P0 := by
    rw [hSd, hP1, hP0, ← hindep b, ← hindep nb, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    by_cases hsp : rowSP c (fun k ↦ (τ k).1) t
    · simp only [nspw_of_SP hsp, hsp, ↓reduceIte]; ring
    · simp only [nspw_of_not_SP hsp, hsp, ↓reduceIte]; ring
  have hB : Q + γ * (P1 + P0) = P1 + P0 := by
    rw [hQd, mul_add, hP1, hP0, ← hindep b, ← hindep nb, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    by_cases hsp : rowSP c (fun k ↦ (τ k).1) t
    · simp only [nspw_of_SP hsp, hsp, ↓reduceIte]; ring
    · simp only [nspw_of_not_SP hsp, hsp, ↓reduceIte]; ring
  have hsplit : ∀ x : ℝ≥0∞, x = (1 - γ) * x + γ * x := fun x ↦ by
    rw [← add_mul, tsub_add_cancel_of_le hγ, one_mul]
  have hfin1 : γ * P1 ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (mul_le_one' hγ hP1le)
  have hfin2 : γ * (P1 + P0) ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top one_ne_top hγ)
      (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top one_ne_top hP1le,
        ne_top_of_le_ne_top one_ne_top hP0le⟩)
  have hSeq : S = (1 - γ) * P1 + γ * P0 := by
    have h3 : S + γ * P1 = ((1 - γ) * P1 + γ * P0) + γ * P1 :=
      calc S + γ * P1 = P1 + γ * P0 := hA
        _ = ((1 - γ) * P1 + γ * P1) + γ * P0 := by rw [← hsplit]
        _ = _ := add_right_comm _ _ _
    exact (ENNReal.add_left_inj hfin1).1 h3
  have hQeq : Q = (1 - γ) * (P1 + P0) := by
    have h3 : Q + γ * (P1 + P0) = (1 - γ) * (P1 + P0) + γ * (P1 + P0) := by
      rw [hB, ← hsplit]
    exact (ENNReal.add_left_inj hfin2).1 h3
  calc S = (1 - γ) * P1 + γ * P0 := hSeq
    _ ≤ (1 - γ) * P1 + ((1 - γ) + (γ - (1 - γ))) * P0 :=
        add_le_add le_rfl (mul_le_mul' le_add_tsub le_rfl)
    _ = (1 - γ) * (P1 + P0) + (γ - (1 - γ)) * P0 := by ring
    _ ≤ (1 - γ) * (P1 + P0) + (γ - (1 - γ)) * 1 :=
        add_le_add le_rfl (mul_le_mul' le_rfl hP0le)
    _ = Q + (γ - (1 - γ)) := by rw [hQeq, mul_one]

include hobs hadd hV in
/-- Normalised form: if the average weight is at most one, success exceeds the baseline by at
most `max 0 (2γ − 1) + 8 q / √|Y|`. -/
theorem dspr_embedded_normalised [Nonempty Z] [Nontrivial Y]
    (hW : dsprEmbWeight o w ≤ 1) :
    dsprEmbSucc e F c o M V tw b w ≤ dsprEmbSP e F c o M V tw w +
      (((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) -
          (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1))) +
        8 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) := by
  obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
  have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
  have hXD : Fintype.card (Tw × Msg → NZ Y) ≠ 0 := Fintype.card_ne_zero
  set cXY : ℝ≥0∞ := (Fintype.card (Tw × Msg → Y) : ℝ≥0∞) with hcXY
  set cXD : ℝ≥0∞ := (Fintype.card (Tw × Msg → NZ Y) : ℝ≥0∞) with hcXD
  have iXD : cXD * cXD⁻¹ = 1 := natCast_mul_inv_cancel hXD
  set κ : ℝ≥0∞ := cXY⁻¹ * cXD⁻¹ with hκ
  have hκ' : ∀ x : ℝ≥0∞, cXD * (κ * x) = cXY⁻¹ * x := by
    intro x
    calc cXD * (κ * x) = (cXD * cXD⁻¹) * (cXY⁻¹ * x) := by rw [hκ]; ring
      _ = cXY⁻¹ * x := by rw [iXD, one_mul]
  have hw : ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) ≤ 1 := by
    have h := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y) (fun H ↦ κ * w (o H))
    rw [h, Finset.mul_sum]
    exact le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ hκ' _)) hW
  have hreal : ∀ Ev : (Tw × Msg → Y) → Leaf → Prop,
      ∑ R : Tw × Msg → Y, cXY⁻¹ * (w (o R) * (M (o R)).prob (patch F e R) (Ev R)) =
        ∑ τ : Tw × Msg → Y × NZ Y, κ * w (o (fun k ↦ (τ k).1)) *
          (M (o (fun k ↦ (τ k).1))).prob (patch F e (fun k ↦ (τ k).1))
            (Ev (fun k ↦ (τ k).1)) := by
    intro Ev
    have e' := sum_fst_comp (X := Tw × Msg) (A := Y) (B := NZ Y)
      (fun H ↦ κ * w (o H) * (M (o H)).prob (patch F e H) (Ev H))
    refine Eq.trans ?_ e'.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [mul_assoc κ]
    exact (hκ' _).symm
  have hid := ((hidden_sg_obs (Y := Y) c o hobs κ).reweight (fun v ↦ w v.1)).map_emb e
  have hS : ∀ (τ : Tw × Msg → Y × NZ Y) (z : Z),
      patch F e (fun k ↦ (τ k).1) z ≠ patch F e (sgG c τ) z →
        z ∈ (sgMarked c (fun k ↦ (τ k).1)).map e := by
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
    · exact (h (by rw [patch_of_not_range _ _ _ _ hz, patch_of_not_range _ _ _ _ hz])).elim
  have h1 := hid.real_le_hyb_add_world hw (fun v ↦ M v.1)
    (fun τ ↦ patch F e (fun k ↦ (τ k).1)) (fun v ↦ patch F e v.2) hS
    (fun τ ↦ dsprEvS c o V tw b (fun k ↦ (τ k).1))
  have h2 := hid.hyb_le_real_add_world hw (fun v ↦ M v.1)
    (fun τ ↦ patch F e (fun k ↦ (τ k).1)) (fun v ↦ patch F e v.2) hS
    (fun τ ↦ dsprEvP c o V tw (fun k ↦ (τ k).1))
  have hh := dspr_hybrid_le e F c o hobs M hadd V tw b hV w κ hw
  unfold dsprEmbSucc dsprEmbSP
  rw [hreal (dsprEvS c o V tw b), hreal (dsprEvP c o V tw)]
  refine h1.trans ((add_le_add hh le_rfl).trans
    ((add_le_add (add_le_add h2 le_rfl) le_rfl).trans (le_of_eq ?_)))
  ring

theorem dsprEmbSucc_smul (s : ℝ≥0∞) :
    dsprEmbSucc e F c o M V tw b (fun a ↦ s * w a) = s * dsprEmbSucc e F c o M V tw b w := by
  unfold dsprEmbSucc
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun R _ ↦ by ring

theorem dsprEmbSP_smul (s : ℝ≥0∞) :
    dsprEmbSP e F c o M V tw (fun a ↦ s * w a) = s * dsprEmbSP e F c o M V tw w := by
  unfold dsprEmbSP
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun R _ ↦ by ring

theorem dsprEmbWeight_smul (s : ℝ≥0∞) :
    dsprEmbWeight o (fun a ↦ s * w a) = s * dsprEmbWeight o w := by
  unfold dsprEmbWeight
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun R _ ↦ by ring

theorem dsprEmbSucc_le_weight [Nonempty Z] :
    dsprEmbSucc e F c o M V tw b w ≤ dsprEmbWeight o w := by
  unfold dsprEmbSucc dsprEmbWeight
  gcongr with R _
  calc w (o R) * (M (o R)).prob (patch F e R) (dsprEvS c o V tw b R) ≤ w (o R) * 1 := by
        gcongr
        exact (M _).prob_le_one _ _
    _ = _ := mul_one _

include hobs hadd hV in
/-- **DSPR on an embedded row, multi-target, weighted.**  For additive models, the weighted
success probability exceeds the weighted baseline (`SPprob`) by at most
`(max 0 (2γ − 1) + 8 q / √|Y|)` times the average weight, `γ = (1 − 1/|Y|)^(|Msg| − 1)`.  (The
weights must be finite.) -/
theorem dspr_embedded_weighted_le [Nonempty Z] [Nontrivial Y] (hwfin : ∀ a, w a ≠ ⊤) :
    dsprEmbSucc e F c o M V tw b w ≤ dsprEmbSP e F c o M V tw w +
      (((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) -
          (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1))) +
        8 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) * dsprEmbWeight o w := by
  set W : ℝ≥0∞ := dsprEmbWeight o w with hWdef
  set δ : ℝ≥0∞ := ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1) -
      (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card Msg - 1))) +
    8 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) with hδ
  have hR := dsprEmbSucc_le_weight e F c o M V tw b w
  by_cases h0 : W = 0
  · rw [← hWdef, h0] at hR
    exact hR.trans zero_le
  have htop : W ≠ ⊤ := by
    rw [hWdef]
    unfold dsprEmbWeight
    refine ENNReal.sum_ne_top.2 fun R _ ↦ ENNReal.mul_ne_top ?_ (hwfin _)
    exact ENNReal.inv_ne_top.2 (by exact_mod_cast Fintype.card_ne_zero)
  have iW : W * W⁻¹ = 1 := ENNReal.mul_inv_cancel h0 htop
  have hn := dspr_embedded_normalised e F c o hobs M hadd V tw b hV (fun a ↦ W⁻¹ * w a) (by
    rw [dsprEmbWeight_smul]
    exact le_of_eq (by rw [mul_comm]; exact iW))
  rw [dsprEmbSucc_smul, dsprEmbSP_smul] at hn
  calc dsprEmbSucc e F c o M V tw b w
      = W * (W⁻¹ * dsprEmbSucc e F c o M V tw b w) := by rw [← mul_assoc, iW, one_mul]
    _ ≤ W * (W⁻¹ * dsprEmbSP e F c o M V tw w + δ) := mul_le_mul' le_rfl hn
    _ = (W * W⁻¹) * dsprEmbSP e F c o M V tw w + δ * W := by ring
    _ = _ := by rw [iW, one_mul]

end Main

end PQ.QROM

#print axioms PQ.QROM.dspr_row_indep
#print axioms PQ.QROM.dspr_hybrid_le
#print axioms PQ.QROM.dspr_embedded_weighted_le
