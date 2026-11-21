import PQ.QROM.ExactDsprTightCore
import PQ.QROM.ExactDsprClosed
import PQ.QROM.DsprCard
import PQ.QROM.ExactZeroPre

/-!
# Target-count-free tight DSPR in the exact two-phase game

`ExactDsprTightCore` proves the abstract/program-level rows bound (`Rows.rows_adv_le`, constant
`168`).  This file instantiates it in the exact SM-DT-DSPR (source final validity) game:

* `MarkLaw`, `markLaw_of_obs`, `fv_markLaw`: in the resampling coupling, given the observation
  and the hybrid row function, the second preimages of the targets are independent marks of
  probability `1/|Y|` (PROVED; it is a definition used as an intermediate hypothesis, discharged
  by `fv_markLaw`).
* `dspr_embedded_tight`, `dspr_leaf_tight`, `dsprSuccHyb_le_SPHyb_add_tight`.
* `dspr_exact_tight`: `Success − SPprob ≤ g + 168 q₂²/|Y| + 2·seedLoss Sd q₁` for
  `g ≥ max 0 (2γ − 1)`.
* `dspr_exact_tight_of_card`, `dspr_exact_tight_zeroPre_of_card`: for `2 ≤ |Y| ≤ |Msg|`,
  `Success − SPprob ≤ 168 q₂²/|Y| (+ 2·seedLoss Sd q₁)`.

The bound does not depend on the number of targets.  The constant `168` is not optimised.

Literature status: a single-target quantum bound for random functions is in the literature
(Bernstein–Hülsing, ePrint 2019/492); whether a target-count-free multi-target tweaked bound is
established is unverified.  No novelty is claimed here.
-/

open Quantum Matrix Finset MeasureTheory ENNReal
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM.Rows

open PQ.QROM.Tight PQ.QROM.Purify

/-- A probability functional `f H E` (probability of the leaf event `E` when the oracle is `H`)
satisfies the target-count-free rows bound with `q` queries. -/
def RowsBound {Z Y Leaf : Type} [Fintype Z] [DecidableEq Z]
    (f : (Z → Y) → (Leaf → Prop) → ℝ) (q : ℕ) : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (p : Z → ℝ) (r : ℝ) (row : Z → J) (G h : Z → Y)
    (Ev : J → Leaf → Prop), (∀ k, 0 ≤ p k) → (∀ k, p k ≤ 1) → 0 ≤ r → (∀ k, p k ≤ r ^ 2) →
    (∀ i j l, Ev i l → Ev j l → i = j) → ∀ g : ℝ, 0 ≤ g →
    (∀ j, (∃ l, Ev j l) → 2 * gam p row j - 1 ≤ g) →
    ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) * f (Hw G h s) (Ev j) ≤
      g + 168 * (q : ℝ) ^ 2 * r ^ 2

/-- **The per-leaf model of a second phase satisfies the rows bound.** -/
theorem ofSecondPort_rowsBound {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
    (I : L.Interp) (F : X → Y) (x : QuantumComp L (qrom2Spec X Y) W A)
    (σ : Matrix (A × Unit) (A × Unit) ℂ) (hσ : σ.PosSemidef) (q : ℕ)
    (hx : x.IsQueryBound (secondBudget q)) {Leaf : Type} (dec : (Σ u, W u) → Leaf) :
    RowsBound (fun H E ↦ ((HybridModel.ofSecondPort I F x σ hσ q hx dec).prob H E).toReal) q := by
  intro J _ _ p r row G h Ev hp0 hp1 hr hpr hdisj g hg0 hg
  have hmain := rows_adv_le p hp0 hp1 r hr hpr row G h F I (fun j l ↦ Ev j (dec l))
    (fun i j l hi hj ↦ hdisj i j (dec l) hi hj) x (secondBudget q) hx hσ g hg0
    (fun j ⟨l, hl⟩ ↦ hg j ⟨dec l, hl⟩)
  have hq : secondBudget q true = q := by simp [secondBudget]
  rw [hq] at hmain
  have htr : 0 ≤ σ.trace.re := hσ.trace_re_nonneg
  have hp : ∀ (H : X → Y) (E : Leaf → Prop),
      ((HybridModel.ofSecondPort I F x σ hσ q hx dec).prob H E).toReal =
      (leafProb (twoRuntime (ports F H)) I x σ (fun l ↦ E (dec l))).toReal * (σ.trace.re)⁻¹ := by
    intro H E
    change (leafProb (twoRuntime (ports F H)) I x σ (fun l ↦ E (dec l)) *
      (ENNReal.ofReal σ.trace.re)⁻¹).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal htr]
  simp only [hp]
  have e : ∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
      ((leafProb (twoRuntime (ports F (Hw G h s))) I x σ (fun l ↦ Ev j (dec l))).toReal *
        (σ.trace.re)⁻¹) =
      (∑ s, bw p s * ∑ j, (if rowClean row j s then (1 : ℝ) else -1) *
        (leafProb (twoRuntime (ports F (Hw G h s))) I x σ (fun l ↦ Ev j (dec l))).toReal) *
        (σ.trace.re)⁻¹ := by
    simp only [Finset.sum_mul, mul_assoc]
  rw [e]
  have hq2 : (0 : ℝ) ≤ 168 * (q : ℝ) ^ 2 * r ^ 2 := by positivity
  rcases htr.eq_or_lt with h0 | hpos
  · rw [← h0, _root_.inv_zero, mul_zero]
    linarith
  · calc _ ≤ (g + 168 * (q : ℝ) ^ 2 * r ^ 2) * σ.trace.re * (σ.trace.re)⁻¹ :=
        mul_le_mul_of_nonneg_right hmain (inv_nonneg.2 htr)
      _ = _ := by field_simp

/-- The probability that a row is clean, as a product over its points. -/
theorem gam_eq_prod {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J] (p : X → ℝ)
    (row : X → J) (j : J) : gam p row j = ∏ k, (if row k = j then 1 - p k else 1) := by
  classical
  have e : ∀ s : X → Bool, bw p s * (if rowClean row j s then (1 : ℝ) else 0) =
      ∏ k, (if s k then p k else 1 - p k) *
        (if row k = j ∧ s k = true then (0 : ℝ) else 1) := by
    intro s
    rw [Finset.prod_mul_distrib]
    congr 1
    by_cases hs : rowClean row j s
    · simp only [hs, ↓reduceIte]
      refine (Finset.prod_eq_one fun k _ ↦ ?_).symm
      by_cases hk : row k = j
      · simp [hk, hs k hk]
      · simp [hk]
    · simp only [hs, ↓reduceIte]
      obtain ⟨k, hk⟩ := not_forall.1 hs
      obtain ⟨hk1, hk2⟩ := Classical.not_imp.1 hk
      refine (Finset.prod_eq_zero (Finset.mem_univ k) ?_).symm
      simp [hk1, Bool.eq_true_of_not_eq_false hk2]
  unfold gam
  simp only [e]
  rw [sum_prod_bool fun k b ↦ (if b then p k else 1 - p k) *
    (if row k = j ∧ b = true then (0 : ℝ) else 1)]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  by_cases hk : row k = j <;> simp [hk]

end PQ.QROM.Rows

namespace PQ.QROM

open PQ.QROM.Rows

/-! ## The DSPR coupling as independent point marks -/

section Marks

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  (e : Tw × Msg ↪ Z) (F : Z → Y) (c : Tw → Option Msg)

/-- A candidate point: a non-target point of a tweak that has a target. -/
def dsprCand (k : Tw × Msg) : Prop := ∃ m, c k.1 = some m ∧ k.2 ≠ m

open Classical in
/-- The mark pattern, on the embedded domain, of a row function: the second preimages of the
targets. -/
noncomputable def markZ (R : Tw × Msg → Y) : Z → Bool :=
  fun z ↦ decide (∃ k, e k = z ∧ k ∈ sgMarked c R)

open Classical in
/-- The mark probabilities: `1/|Y|` at the candidate points, `0` elsewhere. -/
noncomputable def pZ (Y : Type) [Fintype Y] : Z → ℝ :=
  fun z ↦ if ∃ k, e k = z ∧ dsprCand c k then (Fintype.card Y : ℝ)⁻¹ else 0

open Classical in
/-- The rows of the embedded domain: the tweak of an embedded point. -/
noncomputable def rowZ : Z → Option Tw :=
  fun z ↦ if h : ∃ k, e k = z then some (Classical.choose h).1 else none

/-- The values taken at marked points: the target value of the row, read off the hybrid row
function. -/
noncomputable def hZ (g : Tw × Msg → Y) : Z → Y :=
  patch F e fun k ↦ (c k.1).elim (g k) fun m ↦ g (k.1, m)

theorem markZ_apply (R : Tw × Msg → Y) (k : Tw × Msg) :
    markZ e c R (e k) = true ↔ k ∈ sgMarked c R := by
  classical
  simp only [markZ, decide_eq_true_eq]
  constructor
  · rintro ⟨k', hk', hm⟩
    rwa [← e.injective hk']
  · exact fun h ↦ ⟨k, rfl, h⟩

theorem rowZ_apply (k : Tw × Msg) : rowZ e (e k) = some k.1 := by
  have h : ∃ k', e k' = e k := ⟨k, rfl⟩
  unfold rowZ
  simp only [h, ↓reduceDIte]
  rw [e.injective (Classical.choose_spec h)]

theorem rowZ_eq_some {z : Z} {t : Tw} (h : rowZ e z = some t) : ∃ m, e (t, m) = z := by
  unfold rowZ at h
  split_ifs at h with hz
  have h2 : (Classical.choose hz).1 = t := Option.some.inj h
  exact ⟨(Classical.choose hz).2, by rw [← h2]; exact Classical.choose_spec hz⟩

/-- **The real row function is the hybrid one with the marked points set to the target values.** -/
theorem patch_eq_Hw (τ : Tw × Msg → Y × NZ Y) :
    patch F e (fun k ↦ (τ k).1) =
      Hw (patch F e (sgG c τ)) (hZ e F c (sgG c τ)) (markZ e c fun k ↦ (τ k).1) := by
  classical
  funext z
  by_cases hz : ∃ k, e k = z
  · obtain ⟨k, rfl⟩ := hz
    unfold Hw hZ
    rw [patch_apply, patch_apply, patch_apply]
    by_cases hm : k ∈ sgMarked c (fun k ↦ (τ k).1)
    · rw [(markZ_apply e c _ k).2 hm]
      simp only [↓reduceIte]
      simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      obtain ⟨m, hc, hne, heq⟩ := hm
      simp [hc, sgG, heq]
    · have hf : markZ e c (fun k ↦ (τ k).1) (e k) = false := by
        rw [← Bool.not_eq_true]
        exact fun h ↦ hm ((markZ_apply e c _ k).1 h)
      rw [hf]
      simp only [Bool.false_eq_true, ite_false]
      simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      cases hc : c k.1 with
      | none => simp [sgG, hc]
      | some m =>
        by_cases hk : k.2 = m
        · simp [sgG, hc, hk]
        · have hne : (τ k).1 ≠ (τ (k.1, m)).1 := fun h ↦ hm ⟨m, hc, hk, h⟩
          simp [sgG, hc, hk, resample, hne]
  · have hf : markZ e c (fun k ↦ (τ k).1) z = false := by
      simp only [markZ, decide_eq_false_iff_not]
      exact fun ⟨k, hk, _⟩ ↦ hz ⟨k, hk⟩
    unfold Hw
    rw [hf, patch_of_not_range _ _ _ _ hz]
    simp only [Bool.false_eq_true, ite_false]
    rw [patch_of_not_range _ _ _ _ hz]

/-- The row of the tweak `t` is clean iff its target has no second preimage. -/
theorem rowClean_markZ (R : Tw × Msg → Y) (t : Tw) :
    rowClean (rowZ e) (some t) (markZ e c R) ↔ ¬ rowSP c R t := by
  constructor
  · rintro h ⟨m, hc, m', hne, heq⟩
    have h1 := h (e (t, m')) (rowZ_apply e (t, m'))
    have h2 : (t, m') ∈ sgMarked c R := by
      simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨m, hc, hne, heq⟩
    rw [(markZ_apply e c R _).2 h2] at h1
    exact Bool.noConfusion h1
  · intro h z hz
    obtain ⟨m', rfl⟩ := rowZ_eq_some e hz
    rw [← Bool.not_eq_true]
    intro hm
    have := (markZ_apply e c R _).1 hm
    simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨m, hc, hne, heq⟩ := this
    exact h ⟨m, hc, m', hne, heq⟩

/-- The probability that the row of a tweak with a target is clean. -/
theorem gam_target (t : Tw) (m : Msg) (hc : c t = some m) :
    gam (pZ e c Y) (rowZ e) (some t) =
      (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card Msg - 1) := by
  classical
  let et : Msg ↪ Z := ⟨fun m' ↦ e (t, m'), fun a b h ↦ (Prod.ext_iff.1 (e.injective h)).2⟩
  have hrow : ∀ z, rowZ e z = some t ↔ z ∈ (Finset.univ : Finset Msg).map et := by
    intro z
    rw [Finset.mem_map]
    constructor
    · intro h
      obtain ⟨m', hm'⟩ := rowZ_eq_some e h
      exact ⟨m', Finset.mem_univ _, hm'⟩
    · rintro ⟨m', -, rfl⟩
      exact rowZ_apply e (t, m')
  have hp : ∀ m' : Msg, pZ e c Y (et m') = if m' ≠ m then (Fintype.card Y : ℝ)⁻¹ else 0 := by
    intro m'
    have : (∃ k, e k = et m' ∧ dsprCand c k) ↔ m' ≠ m := by
      constructor
      · rintro ⟨k, hk, m₁, hc1, hne⟩
        have hk' : k = (t, m') := e.injective hk
        subst hk'
        have : m₁ = m := Option.some.inj (hc1.symm.trans hc)
        rw [← this]
        exact hne
      · exact fun hne ↦ ⟨(t, m'), rfl, m, hc, hne⟩
    simp only [pZ, this]
  rw [gam_eq_prod]
  simp only [hrow]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_map]
  simp only [hp]
  have e2 : ∀ m' : Msg, (1 - if m' ≠ m then (Fintype.card Y : ℝ)⁻¹ else 0) =
      if m' ≠ m then 1 - (Fintype.card Y : ℝ)⁻¹ else 1 := fun m' ↦ by split_ifs <;> simp
  simp only [e2]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
    Finset.filter_ne' Finset.univ m, Finset.card_erase_of_mem (Finset.mem_univ m),
    Finset.card_univ]

end Marks

/-! ## The embedded DSPR lemma, tight -/

section EmbeddedTight

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Leaf : Type} {q : ℕ} {A : Type}
  (e : Tw × Msg ↪ Z) (F : Z → Y) (c : Tw → Option Msg) (o : (Tw × Msg → Y) → A)
  (M : A → HybridModel Z Y Leaf q) (hadd : ∀ a, (M a).Additive)
  (V : A → Leaf → Prop) (tw : A → Leaf → Tw) (b : A → Leaf → Prop)
  (hV : ∀ a l, V a l → ∃ m, c (tw a l) = some m)

/-- **The law of the marks given the view** (the one probabilistic fact about the coupling used
by the tight bound): in the resampling coupling `τ`, given the observation and the hybrid row
function, the second preimages of the targets form a pattern of independent marks, each
candidate point being marked with probability `1/|Y|`. -/
def MarkLaw : Prop :=
  ∀ Φ : A → (Tw × Msg → Y) → (Z → Bool) → ℝ,
    ∑ τ : Tw × Msg → Y × NZ Y,
        Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1) =
      ∑ τ : Tw × Msg → Y × NZ Y, ∑ π : Z → Bool,
        bw (pZ e c Y) π * Φ (o fun k ↦ (τ k).1) (sgG c τ) π

/-- The output events: valid, the chosen tweak is `t`, and the bit says "no second preimage". -/
def dsprOutEv (a : A) : Option Tw → Leaf → Prop
  | none, _ => False
  | some t, l => V a l ∧ tw a l = t ∧ ¬ b a l

include hadd in
/-- Success minus baseline, for a fixed row function, as a signed sum over the output tweak. -/
theorem dspr_diff_eq [Nonempty Z] (R : Tw × Msg → Y) (H : Z → Y) :
    ((M (o R)).prob H (dsprEvS c o V tw b R)).toReal -
        ((M (o R)).prob H (dsprEvP c o V tw R)).toReal =
      ∑ j : Option Tw, (if rowClean (rowZ e) j (markZ e c R) then (1 : ℝ) else -1) *
        ((M (o R)).prob H (dsprOutEv V tw b (o R) j)).toReal := by
  classical
  have hfin : ∀ E : Leaf → Prop, (M (o R)).prob H E ≠ ⊤ := fun E ↦
    ne_top_of_le_ne_top one_ne_top ((M (o R)).prob_le_one H E)
  have hS := dspr_prob_succ (hadd (o R)) H (V (o R)) (tw (o R)) (b (o R)) (rowSP c R)
  have hP := dspr_prob_sp (hadd (o R)) H (V (o R)) (tw (o R)) (b (o R)) (rowSP c R)
  have hS' : (M (o R)).prob H (dsprEvS c o V tw b R) = _ := hS
  have hP' : (M (o R)).prob H (dsprEvP c o V tw R) = _ := hP
  rw [hS', hP', ENNReal.toReal_sum (fun t _ ↦ by split_ifs <;> exact hfin _),
    ENNReal.toReal_sum (fun t _ ↦ by
      split_ifs
      · exact ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩
      · exact ENNReal.zero_ne_top),
    ← Finset.sum_sub_distrib, Fintype.sum_option]
  have hnone : (M (o R)).prob H (dsprOutEv V tw b (o R) none) = 0 :=
    (hadd (o R)).prob_false H
  rw [hnone, ENNReal.toReal_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases hsp : rowSP c R t
  · have hcl : ¬ rowClean (rowZ e) (some t) (markZ e c R) := fun h' ↦
      (rowClean_markZ e c R t).1 h' hsp
    simp only [hsp, hcl, ite_true, ite_false]
    rw [ENNReal.toReal_add (hfin _) (hfin _)]
    change _ = -1 * ((M (o R)).prob H (fun l ↦ V (o R) l ∧ tw (o R) l = t ∧ ¬ b (o R) l)).toReal
    ring
  · have hcl : rowClean (rowZ e) (some t) (markZ e c R) := (rowClean_markZ e c R t).2 hsp
    simp only [hsp, hcl, ite_true, ite_false, ENNReal.toReal_zero, sub_zero, one_mul]
    rfl

include hadd hV in
/-- **DSPR on an embedded row, tight and independent of the number of targets.**  For additive
models satisfying the rows bound, the weighted success exceeds the weighted baseline by at most
`(g + 168 q² / |Y|)` times the total weight, where `2 γ − 1 ≤ g`,
`γ = (1 − 1/|Y|)^(|Msg| − 1)`.  (Conditional on the law of the marks, `MarkLaw`.) -/
theorem dspr_embedded_tight [Nonempty Z] [Nontrivial Y]
    (hrows : ∀ a, RowsBound (fun H E ↦ ((M a).prob H E).toReal) q)
    (hML : MarkLaw e c o) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (g : ℝ) (hg0 : 0 ≤ g)
    (hg : 2 * (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card Msg - 1) - 1 ≤ g) :
    ∑ R : Tw × Msg → Y, w (o R) *
        (((M (o R)).prob (patch F e R) (dsprEvS c o V tw b R)).toReal -
          ((M (o R)).prob (patch F e R) (dsprEvP c o V tw R)).toReal) ≤
      (g + 168 * (q : ℝ) ^ 2 / Fintype.card Y) * ∑ R : Tw × Msg → Y, w (o R) := by
  classical
  obtain ⟨d₀, hd₀⟩ := exists_ne (0 : Y)
  have : Nonempty (NZ Y) := ⟨⟨d₀, hd₀⟩⟩
  have hcD : (0 : ℝ) < Fintype.card (Tw × Msg → NZ Y) := by
    exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hN1 : (Fintype.card Y : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α := Y))
  set r : ℝ := Real.sqrt ((Fintype.card Y : ℝ)⁻¹) with hrdef
  have hr2 : r ^ 2 = (Fintype.card Y : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  let Φ : A → (Tw × Msg → Y) → (Z → Bool) → ℝ := fun a g' π ↦
    w a * ∑ j : Option Tw, (if rowClean (rowZ e) j π then (1 : ℝ) else -1) *
      ((M a).prob (Hw (patch F e g') (hZ e F c g') π) (dsprOutEv V tw b a j)).toReal
  have h1 : ∀ τ : Tw × Msg → Y × NZ Y,
      w (o fun k ↦ (τ k).1) *
        (((M (o fun k ↦ (τ k).1)).prob (patch F e fun k ↦ (τ k).1)
            (dsprEvS c o V tw b fun k ↦ (τ k).1)).toReal -
          ((M (o fun k ↦ (τ k).1)).prob (patch F e fun k ↦ (τ k).1)
            (dsprEvP c o V tw fun k ↦ (τ k).1)).toReal) =
      Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1) := by
    intro τ
    rw [dspr_diff_eq e c o M hadd V tw b (fun k ↦ (τ k).1)]
    simp only [Φ]
    rw [← patch_eq_Hw e F c τ]
  have h2 : ∀ (a : A) (g' : Tw × Msg → Y),
      ∑ π : Z → Bool, bw (pZ e c Y) π * Φ a g' π ≤
        w a * (g + 168 * (q : ℝ) ^ 2 / Fintype.card Y) := by
    intro a g'
    have hb := hrows a (Option Tw) (pZ e c Y) r (rowZ e) (patch F e g') (hZ e F c g')
      (dsprOutEv V tw b a)
      (fun k ↦ by unfold pZ; split_ifs <;> positivity)
      (fun k ↦ by
        unfold pZ
        split_ifs
        · exact hN1
        · exact zero_le_one)
      (Real.sqrt_nonneg _)
      (fun k ↦ by
        rw [hr2]
        unfold pZ
        split_ifs
        · exact le_rfl
        · positivity)
      (fun i j l hi hj ↦ by
        cases i with
        | none => exact hi.elim
        | some t =>
          cases j with
          | none => exact hj.elim
          | some t' => exact congrArg some (hi.2.1.symm.trans hj.2.1))
      g hg0
      (fun j ⟨l, hl⟩ ↦ by
        cases j with
        | none => exact hl.elim
        | some t =>
          obtain ⟨m, hm⟩ := hV a l hl.1
          rw [hl.2.1] at hm
          rw [gam_target e c t m hm]
          exact hg)
    rw [hr2] at hb
    calc ∑ π : Z → Bool, bw (pZ e c Y) π * Φ a g' π
        = w a * ∑ π : Z → Bool, bw (pZ e c Y) π * ∑ j : Option Tw,
            (if rowClean (rowZ e) j π then (1 : ℝ) else -1) *
              ((M a).prob (Hw (patch F e g') (hZ e F c g') π) (dsprOutEv V tw b a j)).toReal := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun π _ ↦ by simp only [Φ]; ring
      _ ≤ w a * (g + 168 * (q : ℝ) ^ 2 * (Fintype.card Y : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hb (hw a)
      _ = _ := by rw [div_eq_mul_inv]
  have hfst := fun f : (Tw × Msg → Y) → ℝ ↦
    PQ.QROM.Tight.sum_fst_comp_real (X := Tw × Msg) (A := Y) (B := NZ Y) f
  have hL := hfst fun R ↦ w (o R) *
    (((M (o R)).prob (patch F e R) (dsprEvS c o V tw b R)).toReal -
      ((M (o R)).prob (patch F e R) (dsprEvP c o V tw R)).toReal)
  have hW := hfst fun R ↦ w (o R)
  have hmain : (Fintype.card (Tw × Msg → NZ Y) : ℝ) * ∑ R : Tw × Msg → Y, w (o R) *
      (((M (o R)).prob (patch F e R) (dsprEvS c o V tw b R)).toReal -
        ((M (o R)).prob (patch F e R) (dsprEvP c o V tw R)).toReal) ≤
      (Fintype.card (Tw × Msg → NZ Y) : ℝ) *
        ((g + 168 * (q : ℝ) ^ 2 / Fintype.card Y) * ∑ R : Tw × Msg → Y, w (o R)) := by
    rw [← hL, Finset.sum_congr rfl fun τ _ ↦ h1 τ, hML Φ]
    calc _ ≤ ∑ τ : Tw × Msg → Y × NZ Y,
          w (o fun k ↦ (τ k).1) * (g + 168 * (q : ℝ) ^ 2 / Fintype.card Y) :=
          Finset.sum_le_sum fun τ _ ↦ h2 _ _
      _ = _ := by
          rw [← Finset.sum_mul, hW]
          ring
  exact le_of_mul_le_mul_left hmain hcD

end EmbeddedTight

/-! ## The mark law holds for the resampling coupling -/

section MarkLawProof

section Pattern

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Given the hybrid value, a point is marked with probability `1/|Y|` and unmarked with
probability `1 - 1/|Y|`. -/
theorem pattern_fiber (b : Bool) (y z : Y) :
    ∑ t : Y × NZ Y with resample y t = z, (if (t.1 = y ↔ b = true) then (1 : ℝ≥0∞) else 0) =
      ∑ t : Y × NZ Y with resample y t = z,
        (if b = true then (Fintype.card Y : ℝ≥0∞)⁻¹ else 1 - (Fintype.card Y : ℝ≥0∞)⁻¹) := by
  cases b
  · have h := resample_fiber_ne y z
    simp only [Bool.false_eq_true, iff_false, ↓reduceIte]
    convert h using 2
  · have h := resample_fiber y z
    simp only [iff_true, ↓reduceIte]
    convert h using 2

/-- **Independence of the mark pattern.**  For a set `s` of resampled coordinates, each with its
own target value `u k τ`: given the hybrid function, the marks of the points of `s` are
independent, each with probability `1/|Y|`. -/
theorem sum_pattern_prod (s : Finset X) (u : X → (X → Y × NZ Y) → Y) (ρ : X → Bool)
    (hu : ∀ k ∈ s, ∀ (k' : X) (τ : X → Y × NZ Y) (t : Y × NZ Y),
      u k' (Function.update τ k t) = u k' τ)
    (G : (X → Y × NZ Y) → X → Y) (hGk : ∀ k ∈ s, ∀ τ, G τ k = resample (u k τ) (τ k))
    (hG : ∀ k ∈ s, ∀ τ t j, j ≠ k → G (Function.update τ k t) j = G τ j)
    (Ψ : (X → Y × NZ Y) → (X → Y) → ℝ≥0∞)
    (hΨ : ∀ k ∈ s, ∀ τ t g, Ψ (Function.update τ k t) g = Ψ τ g) :
    ∑ τ : X → Y × NZ Y,
        (∏ k ∈ s, if ((τ k).1 = u k τ ↔ ρ k = true) then (1 : ℝ≥0∞) else 0) * Ψ τ (G τ) =
      (∏ k ∈ s, if ρ k = true then (Fintype.card Y : ℝ≥0∞)⁻¹
          else 1 - (Fintype.card Y : ℝ≥0∞)⁻¹) * ∑ τ : X → Y × NZ Y, Ψ τ (G τ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hks : k ∈ insert k s := Finset.mem_insert_self k s
    have e := sum_weight_view k (fun y t ↦ if (t.1 = y ↔ ρ k = true) then (1 : ℝ≥0∞) else 0)
      (if ρ k = true then (Fintype.card Y : ℝ≥0∞)⁻¹ else 1 - (Fintype.card Y : ℝ≥0∞)⁻¹)
      (pattern_fiber (ρ k)) (u k) (hu k hks k) G (hGk k hks) (hG k hks)
      (fun τ g ↦ (∏ k' ∈ s, if ((τ k').1 = u k' τ ↔ ρ k' = true) then (1 : ℝ≥0∞) else 0) *
        Ψ τ g) (by
        intro τ t g
        rw [hΨ k hks]
        congr 1
        refine Finset.prod_congr rfl fun k' hk' ↦ ?_
        have hne : k' ≠ k := fun h ↦ hk (h ▸ hk')
        rw [Function.update_of_ne hne, hu k hks])
    calc ∑ τ : X → Y × NZ Y,
          (∏ k' ∈ insert k s, if ((τ k').1 = u k' τ ↔ ρ k' = true) then (1 : ℝ≥0∞) else 0) *
            Ψ τ (G τ)
        = ∑ τ : X → Y × NZ Y, (if ((τ k).1 = u k τ ↔ ρ k = true) then (1 : ℝ≥0∞) else 0) *
            ((∏ k' ∈ s, if ((τ k').1 = u k' τ ↔ ρ k' = true) then (1 : ℝ≥0∞) else 0) *
              Ψ τ (G τ)) :=
          Finset.sum_congr rfl fun τ _ ↦ by rw [Finset.prod_insert hk, mul_assoc]
      _ = (if ρ k = true then (Fintype.card Y : ℝ≥0∞)⁻¹ else 1 - (Fintype.card Y : ℝ≥0∞)⁻¹) *
            ∑ τ : X → Y × NZ Y,
              (∏ k' ∈ s, if ((τ k').1 = u k' τ ↔ ρ k' = true) then (1 : ℝ≥0∞) else 0) *
                Ψ τ (G τ) := e
      _ = _ := by
          rw [ih (fun k' hk' ↦ hu k' (Finset.mem_insert_of_mem hk'))
            (fun k' hk' ↦ hGk k' (Finset.mem_insert_of_mem hk'))
            (fun k' hk' ↦ hG k' (Finset.mem_insert_of_mem hk'))
            (fun k' hk' ↦ hΨ k' (Finset.mem_insert_of_mem hk')),
            Finset.prod_insert hk, mul_assoc]

end Pattern

variable {Z Tw Msg Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] {A : Type}
  (e : Tw × Msg ↪ Z) (c : Tw → Option Msg) (o : (Tw × Msg → Y) → A)
  (hobs : ∀ (k : Tw × Msg) (m : Msg), c k.1 = some m → k.2 ≠ m →
    ∀ (R : Tw × Msg → Y) (v : Y), o (Function.update R k v) = o R)

include hobs in
open Classical in
/-- The mark law for one pattern, in `ℝ≥0∞`. -/
theorem markLaw_pattern (Ψ : A → (Tw × Msg → Y) → ℝ≥0∞) (π : Z → Bool) :
    ∑ τ : Tw × Msg → Y × NZ Y,
        (if markZ e c (fun k ↦ (τ k).1) = π then (1 : ℝ≥0∞) else 0) *
          Ψ (o fun k ↦ (τ k).1) (sgG c τ) =
      ENNReal.ofReal (bw (pZ e c Y) π) *
        ∑ τ : Tw × Msg → Y × NZ Y, Ψ (o fun k ↦ (τ k).1) (sgG c τ) := by
  let S : Finset (Tw × Msg) := Finset.univ.filter (dsprCand c)
  let u : Tw × Msg → (Tw × Msg → Y × NZ Y) → Y :=
    fun k τ ↦ (c k.1).elim 0 fun m ↦ (τ (k.1, m)).1
  have hS : ∀ k, k ∈ S ↔ dsprCand c k := fun k ↦ by simp [S]
  have hmapS : ∀ z, z ∈ S.map e ↔ ∃ k, e k = z ∧ dsprCand c k := by
    intro z
    rw [Finset.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, rfl, (hS k).1 hk⟩
    · rintro ⟨k, rfl, hk⟩; exact ⟨k, (hS k).2 hk, rfl⟩
  have hcard0 : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos (α := Y)
  have hinv1 : (Fintype.card Y : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α := Y))
  -- marks vanish off the candidates
  have hoff : ∀ (R : Tw × Msg → Y) (z : Z), z ∉ S.map e → markZ e c R z = false := by
    intro R z hz
    by_contra hne
    have ht : markZ e c R z = true := by simpa using hne
    simp only [markZ, decide_eq_true_eq] at ht
    obtain ⟨k, hk, hm⟩ := ht
    obtain ⟨m, hc, hkm, -⟩ := (Finset.mem_filter.1 hm).2
    exact hz ((hmapS z).2 ⟨k, hk, m, hc, hkm⟩)
  -- a candidate is marked iff its value is the target value of its row
  have hmem : ∀ k ∈ S, ∀ τ : Tw × Msg → Y × NZ Y,
      markZ e c (fun k ↦ (τ k).1) (e k) = true ↔ (τ k).1 = u k τ := by
    intro k hk τ
    obtain ⟨m, hc, hkm⟩ := (hS k).1 hk
    rw [markZ_apply]
    simp only [sgMarked, Finset.mem_filter, Finset.mem_univ, true_and, u, hc, Option.elim_some]
    constructor
    · rintro ⟨m', hc', -, h⟩
      have hm : m = m' := by simpa using hc'
      rw [hm]; exact h
    · exact fun h ↦ ⟨m, rfl, hkm, h⟩
  have hmark : ∀ τ : Tw × Msg → Y × NZ Y, markZ e c (fun k ↦ (τ k).1) = π ↔
      (∀ z, z ∉ S.map e → π z = false) ∧ ∀ k ∈ S, ((τ k).1 = u k τ ↔ π (e k) = true) := by
    intro τ
    constructor
    · intro h
      refine ⟨fun z hz ↦ ?_, fun k hk ↦ ?_⟩
      · rw [← h]; exact hoff _ z hz
      · rw [← h]; exact (hmem k hk τ).symm
    · rintro ⟨h1, h2⟩
      funext z
      by_cases hz : z ∈ S.map e
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hz
        rw [Bool.eq_iff_iff]
        exact (hmem k hk τ).trans (h2 k hk)
      · rw [hoff _ z hz, h1 z hz]
  -- the Bernoulli weight
  have hbw : bw (pZ e c Y) π = (if ∀ z, z ∉ S.map e → π z = false then (1 : ℝ) else 0) *
      ∏ k ∈ S, (if π (e k) = true then (Fintype.card Y : ℝ)⁻¹
        else 1 - (Fintype.card Y : ℝ)⁻¹) := by
    unfold bw
    rw [← Finset.prod_mul_prod_compl (S.map e), mul_comm, Finset.prod_map]
    congr 1
    · have : ∀ z ∈ (S.map e)ᶜ, (if π z = true then pZ e c Y z else 1 - pZ e c Y z) =
          if π z = false then (1 : ℝ) else 0 := by
        intro z hz
        have hz' : ¬ ∃ k, e k = z ∧ dsprCand c k := fun h ↦
          (Finset.mem_compl.1 hz) ((hmapS z).2 h)
        have hp : pZ e c Y z = 0 := by simp only [pZ, hz', ↓reduceIte]
        rw [hp]
        cases π z <;> simp
      rw [Finset.prod_congr rfl this, Finset.prod_ite_zero, Finset.prod_const_one]
      simp only [Finset.mem_compl]
    · refine Finset.prod_congr rfl fun k hk ↦ ?_
      have hp : pZ e c Y (e k) = (Fintype.card Y : ℝ)⁻¹ := by
        have : ∃ k', e k' = e k ∧ dsprCand c k' := ⟨k, rfl, (hS k).1 hk⟩
        simp only [pZ, this, ↓reduceIte]
      rw [hp]
  by_cases hOff : ∀ z, z ∉ S.map e → π z = false
  · have hne : ∀ k ∈ S, ∀ (t' : Tw) (m' : Msg), c t' = some m' → (t', m') ≠ k := by
      intro k hk t' m' h heq
      obtain ⟨m, hc, hkm⟩ := (hS k).1 hk
      have e1 : k.1 = t' := by rw [← heq]
      have e2 : k.2 = m' := by rw [← heq]
      rw [← e1, hc] at h
      exact hkm (e2.trans (Option.some.inj h).symm)
    have hind : ∀ τ : Tw × Msg → Y × NZ Y,
        (if markZ e c (fun k ↦ (τ k).1) = π then (1 : ℝ≥0∞) else 0) =
          ∏ k ∈ S, if ((τ k).1 = u k τ ↔ π (e k) = true) then (1 : ℝ≥0∞) else 0 := by
      intro τ
      rw [Finset.prod_ite_zero, Finset.prod_const_one]
      by_cases hm : markZ e c (fun k ↦ (τ k).1) = π
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true ((hmark τ).1 hm).2)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm),
          ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hm ((hmark τ).2 ⟨hOff, h⟩))]
    have key := sum_pattern_prod S u (fun k ↦ π (e k))
      (fun k hk k' τ v ↦ by
        cases hck : c k'.1 with
        | none => simp [u, hck]
        | some m' => simp [u, hck, Function.update_of_ne (hne k hk k'.1 m' hck)])
      (sgG c)
      (fun k hk τ ↦ by
        obtain ⟨m, hc, hkm⟩ := (hS k).1 hk
        simp [sgG, u, hc, hkm])
      (fun k hk τ v j hj ↦ by
        cases hcj : c j.1 with
        | none => simp [sgG, hcj, Function.update_of_ne hj]
        | some m' =>
          simp [sgG, hcj, Function.update_of_ne hj, Function.update_of_ne (hne k hk j.1 m' hcj)])
      (fun τ g ↦ Ψ (o fun k ↦ (τ k).1) g)
      (fun k hk τ v g ↦ by
        obtain ⟨m, hc, hkm⟩ := (hS k).1 hk
        have : (fun j ↦ (Function.update τ k v j).1) =
            Function.update (fun j ↦ (τ j).1) k v.1 := by
          funext j
          by_cases hj : j = k
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        rw [this, hobs k m hc hkm])
    simp only [hind]
    rw [key, hbw, ite_eq_left_of_eq_true _ _ (eq_true hOff), one_mul,
      ENNReal.ofReal_prod_of_nonneg fun k _ ↦ by
        split_ifs
        · exact inv_nonneg.2 hcard0.le
        · linarith]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    split_ifs
    · rw [ENNReal.ofReal_inv_of_pos hcard0, ENNReal.ofReal_natCast]
    · rw [ENNReal.ofReal_sub _ (inv_nonneg.2 hcard0.le), ENNReal.ofReal_one,
        ENNReal.ofReal_inv_of_pos hcard0, ENNReal.ofReal_natCast]
  · rw [hbw, ite_eq_right_of_eq_false _ _ (eq_false hOff), zero_mul, ENNReal.ofReal_zero, zero_mul]
    refine Finset.sum_eq_zero fun τ _ ↦ ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hOff ((hmark τ).1 h).1), zero_mul]

include hobs in
/-- The mark law for a nonnegative test function. -/
theorem markLaw_nonneg (Φ : A → (Tw × Msg → Y) → (Z → Bool) → ℝ) (hΦ : ∀ a g π, 0 ≤ Φ a g π) :
    ∑ τ : Tw × Msg → Y × NZ Y,
        Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1) =
      ∑ τ : Tw × Msg → Y × NZ Y, ∑ π : Z → Bool,
        bw (pZ e c Y) π * Φ (o fun k ↦ (τ k).1) (sgG c τ) π := by
  classical
  have hp0 : ∀ z, 0 ≤ pZ e c Y z := fun z ↦ by
    unfold pZ; split_ifs
    · exact inv_nonneg.2 (Nat.cast_nonneg _)
    · exact le_rfl
  have hp1 : ∀ z, pZ e c Y z ≤ 1 := fun z ↦ by
    unfold pZ; split_ifs
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α := Y))
    · exact zero_le_one
  have hπ : ∀ π : Z → Bool,
      ∑ τ : Tw × Msg → Y × NZ Y,
          (if markZ e c (fun k ↦ (τ k).1) = π then (1 : ℝ) else 0) *
            Φ (o fun k ↦ (τ k).1) (sgG c τ) π =
        bw (pZ e c Y) π * ∑ τ : Tw × Msg → Y × NZ Y, Φ (o fun k ↦ (τ k).1) (sgG c τ) π := by
    intro π
    have h := congrArg ENNReal.toReal
      (markLaw_pattern e c o hobs (fun a g ↦ ENNReal.ofReal (Φ a g π)) π)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (bw_nonneg _ hp0 hp1 π),
      ENNReal.toReal_sum fun τ _ ↦ ENNReal.ofReal_ne_top,
      ENNReal.toReal_sum fun τ _ ↦ ENNReal.mul_ne_top (by split_ifs <;> simp)
        ENNReal.ofReal_ne_top] at h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hΦ _ _ _)] at h
    rw [← h]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    congr 1
    split_ifs <;> simp
  calc ∑ τ : Tw × Msg → Y × NZ Y,
        Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1)
      = ∑ τ : Tw × Msg → Y × NZ Y, ∑ π : Z → Bool,
          (if markZ e c (fun k ↦ (τ k).1) = π then (1 : ℝ) else 0) *
            Φ (o fun k ↦ (τ k).1) (sgG c τ) π :=
        Finset.sum_congr rfl fun τ _ ↦ by
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = ∑ π : Z → Bool, bw (pZ e c Y) π *
          ∑ τ : Tw × Msg → Y × NZ Y, Φ (o fun k ↦ (τ k).1) (sgG c τ) π := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun π _ ↦ hπ π
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun π _ ↦ Finset.mul_sum _ _ _

include hobs in
/-- **The mark law holds** as soon as the observation does not depend on the values at the
candidate points (non-target points of a tweak with a target). -/
theorem markLaw_of_obs : MarkLaw e c o := by
  intro Φ
  have hd : ∀ x : ℝ, x = max x 0 - max (-x) 0 := fun x ↦ by
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hp := markLaw_nonneg e c o hobs (fun a g π ↦ max (Φ a g π) 0) fun _ _ _ ↦ le_max_right _ _
  have hn := markLaw_nonneg e c o hobs (fun a g π ↦ max (-Φ a g π) 0)
    fun _ _ _ ↦ le_max_right _ _
  calc ∑ τ : Tw × Msg → Y × NZ Y,
        Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1)
      = ∑ τ : Tw × Msg → Y × NZ Y,
          (max (Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1)) 0 -
            max (-Φ (o fun k ↦ (τ k).1) (sgG c τ) (markZ e c fun k ↦ (τ k).1)) 0) :=
        Finset.sum_congr rfl fun τ _ ↦ hd _
    _ = _ := by
        rw [Finset.sum_sub_distrib, hp, hn, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun τ _ ↦ ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun π _ ↦ ?_
        rw [← mul_sub, ← hd]

end MarkLawProof

end PQ.QROM



namespace PQ.QROM

open PQ.QROM.Rows

/-! ## The exact DSPR-FV game -/

theorem ennreal_le_add_of_toReal {a b d : ℝ≥0∞} {c : ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hd : d ≠ ⊤)
    (hc : 0 ≤ c) (h : a.toReal - b.toReal ≤ c * d.toReal) : a ≤ b + ENNReal.ofReal c * d := by
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_toReal hd,
    ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add ENNReal.toReal_nonneg
      (mul_nonneg hc ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem avg_ne_top {T : Type} [Fintype T] (f : T → ℝ≥0∞) (hf : ∀ t, f t ≠ ⊤) : avg f ≠ ⊤ := by
  unfold avg
  refine ENNReal.sum_ne_top.2 fun t _ ↦ ENNReal.mul_ne_top ?_ (hf t)
  exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨t⟩).ne')

theorem toReal_avg_fin {T : Type} [Fintype T] (f : T → ℝ≥0∞) (hf : ∀ t, f t ≠ ⊤) :
    (avg f).toReal = ∑ t, (Fintype.card T : ℝ)⁻¹ * (f t).toReal := by
  unfold avg
  rw [ENNReal.toReal_sum fun t _ ↦ ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨t⟩).ne')) (hf t)]
  exact Finset.sum_congr rfl fun t _ ↦ by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]

section Game

variable {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Bool) u}

/-- **One leaf of phase 1, tight.** -/
theorem dspr_leaf_tight [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × FvState Tw Msg)
    (hML : FvValid cap p.2.2 → MarkLaw (rowEmb P) (fvC p.2.2) (fvSeen (Y := Y) p.2.2))
    (g : ℝ) (hg0 : 0 ≤ g)
    (hg : 2 * (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card Msg - 1) - 1 ≤ g) :
    (avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprWin cap R l.2 p.2.2)) ≤
      (avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprSPWin cap R l.2 p.2.2)) +
        ENNReal.ofReal (g + 168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) *
          avg fun R : Tw × Msg → Y ↦
            ENNReal.ofReal (postOf I ρ fvCh fvInit n x F R p).trace.re := by
  by_cases hv : FvValid cap p.2.2
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    have h0 : ∀ R : Tw × Msg → Y,
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprWin cap R l.2 p.2.2) = 0 := fun R ↦ by
      unfold leafProb
      simp only [tsum_eq_zero_iff]
      intro l
      rw [ind_of_false fun h ↦ hv h.1, mul_zero]
    simp only [h0]
    exact le_antisymm (avg_le fun _ ↦ le_rfl) zero_le
  let τ : (Tw × Msg → Y) → Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
    fun a ↦ postOf I ρ fvCh fvInit n x F a p
  have hτ : ∀ a, (τ a).PosSemidef := fun a ↦ postOf_posSemidef F a p
  let M : (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y (ℕ × Bool) q₂ := fun a ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (τ a) (hτ a) q₂ (h2 P p.1 p.2.1) Sigma.snd
  have hpost : ∀ R : Tw × Msg → Y, postOf I ρ fvCh fvInit n x F R p = τ (fvSeen p.2.2 R) :=
    fun R ↦ postOf_eq_fvSeen F R p
  let V : (Tw × Msg → Y) → ℕ × Bool → Prop := fun _ l ↦ (p.2.2.chal[l.1]?).isSome
  let tw : (Tw × Msg → Y) → ℕ × Bool → Tw := fun _ l ↦
    ((p.2.2.chal[l.1]?).map Prod.fst).getD default
  let b : (Tw × Msg → Y) → ℕ × Bool → Prop := fun _ l ↦ l.2 = true
  have hget : ∀ (j : ℕ) (t : Tw) (m : Msg), p.2.2.chal[j]? = some (t, m) →
      fvC p.2.2 t = some m := fun j t m h ↦ find_of_mem hv.2.1 (List.mem_of_getElem? h)
  have hV : ∀ (a : Tw × Msg → Y) (l : ℕ × Bool), V a l → ∃ m, fvC p.2.2 (tw a l) = some m := by
    intro a l hl
    obtain ⟨⟨t, m⟩, htm⟩ := Option.isSome_iff_exists.1 hl
    refine ⟨m, ?_⟩
    simp only [tw, htm, Option.map_some, Option.getD_some]
    exact hget _ _ _ htm
  have hsp : ∀ (R : Tw × Msg → Y) (t : Tw) (m : Msg), fvC p.2.2 t = some m →
      (rowSP (fvC p.2.2) R t ↔ HasSecondPreimage R t m) := by
    intro R t m hc
    constructor
    · rintro ⟨m₁, h1, m', hne, heq⟩
      have : m₁ = m := Option.some.inj (h1.symm.trans hc)
      subst this
      exact ⟨m', fun h ↦ hne h.symm, heq.symm⟩
    · rintro ⟨m', hne, heq⟩
      exact ⟨m, hc, m', fun h ↦ hne h.symm, heq.symm⟩
  have hevS : ∀ R : Tw × Msg → Y, (fun l : Σ _ : QReg, ℕ × Bool ↦ dsprWin cap R l.2 p.2.2) =
      fun l ↦ dsprEvS (fvC p.2.2) (fvSeen p.2.2) V tw b R (Sigma.snd l) := by
    intro R
    funext l
    apply propext
    constructor
    · rintro ⟨-, t, m, htm, hb⟩
      refine ⟨by show (p.2.2.chal[l.2.1]?).isSome = true; rw [htm]; rfl, ?_⟩
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)]
      exact hb
    · rintro ⟨hl, hb⟩
      obtain ⟨⟨t, m⟩, htm⟩ := Option.isSome_iff_exists.1 hl
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)] at hb
      exact ⟨hv, t, m, htm, hb⟩
  have hevP : ∀ R : Tw × Msg → Y, (fun l : Σ _ : QReg, ℕ × Bool ↦ dsprSPWin cap R l.2 p.2.2) =
      fun l ↦ dsprEvP (fvC p.2.2) (fvSeen p.2.2) V tw R (Sigma.snd l) := by
    intro R
    funext l
    apply propext
    constructor
    · rintro ⟨-, t, m, htm, hb⟩
      refine ⟨by show (p.2.2.chal[l.2.1]?).isSome = true; rw [htm]; rfl, ?_⟩
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)]
      exact hb
    · rintro ⟨hl, hb⟩
      obtain ⟨⟨t, m⟩, htm⟩ := Option.isSome_iff_exists.1 hl
      have htw : tw (fvSeen p.2.2 R) l.2 = t := by simp [tw, htm]
      rw [htw, hsp R t m (hget _ _ _ htm)] at hb
      exact ⟨hv, t, m, htm, hb⟩
  have : Nonempty (Dom Sd Tw Msg) := ⟨(P, (default, Classical.arbitrary Msg))⟩
  have hT := dspr_embedded_tight (rowEmb P) F (fvC p.2.2) (fvSeen p.2.2) M
    (fun a ↦ HybridModel.ofSecondPort_additive I F _ _ _ _ _ _) V tw b hV
    (fun a ↦ ofSecondPort_rowsBound I F _ _ _ _ _ _) (hML hv)
    (fun a ↦ (τ a).trace.re) (fun a ↦ (hτ a).trace_re_nonneg) g hg0 hg
  have hLS : ∀ R : Tw × Msg → Y,
      (leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprWin cap R l.2 p.2.2)).toReal =
      (τ (fvSeen p.2.2 R)).trace.re * ((M (fvSeen p.2.2 R)).prob (patch F (rowEmb P) R)
        (dsprEvS (fvC p.2.2) (fvSeen p.2.2) V tw b R)).toReal := by
    intro R
    rw [hpost R, patchRow_eq_patch, hevS R, ← HybridModel.ofSecondPort_prob I F _ _ (hτ _) q₂
      (h2 P p.1 p.2.1) Sigma.snd, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hτ _).trace_re_nonneg]
  have hLP : ∀ R : Tw × Msg → Y,
      (leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ fvCh fvInit n x F R p) (fun l ↦ dsprSPWin cap R l.2 p.2.2)).toReal =
      (τ (fvSeen p.2.2 R)).trace.re * ((M (fvSeen p.2.2 R)).prob (patch F (rowEmb P) R)
        (dsprEvP (fvC p.2.2) (fvSeen p.2.2) V tw R)).toReal := by
    intro R
    rw [hpost R, patchRow_eq_patch, hevP R, ← HybridModel.ofSecondPort_prob I F _ _ (hτ _) q₂
      (h2 P p.1 p.2.1) Sigma.snd, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hτ _).trace_re_nonneg]
  have hfin : ∀ (R : Tw × Msg → Y) (E : (Σ _ : QReg, ℕ × Bool) → Prop),
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ fvCh fvInit n x F R p) E ≠ ⊤ := fun R E ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (leafProb_le (R := twoRuntime (ports F (patchRow F P R))) (I := I) (ph2 P p.1 p.2.1)
        (σ := postOf I ρ fvCh fvInit n x F R p) (by rw [hpost R]; exact hτ _) E)
  refine ennreal_le_add_of_toReal (avg_ne_top _ fun R ↦ hfin R _) (avg_ne_top _ fun R ↦ hfin R _)
    (avg_ne_top _ fun R ↦ ENNReal.ofReal_ne_top) (by positivity) ?_
  rw [toReal_avg_fin _ fun R ↦ hfin R _, toReal_avg_fin _ fun R ↦ hfin R _,
    toReal_avg_fin _ fun R ↦ ENNReal.ofReal_ne_top, ← Finset.sum_sub_distrib]
  simp only [hLS, hLP]
  simp only [hpost, ENNReal.toReal_ofReal (hτ _).trace_re_nonneg]
  have hc0 : (0 : ℝ) ≤ (Fintype.card (Tw × Msg → Y) : ℝ)⁻¹ := by positivity
  have key := mul_le_mul_of_nonneg_left hT hc0
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun R _ ↦ by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun R _ ↦ by ring

/-- **SM-DT-DSPR, hybrid world, tight**: success exceeds the baseline by at most
`g + 168 q₂² / |Y|`, for any `g ≥ max 0 (2γ − 1)`, `γ = (1 − 1/|Y|)^(|Msg| − 1)`.
Conditional on the mark law `MarkLaw` for every valid final-validity state. -/
theorem dsprSuccHyb_le_SPHyb_add_tight [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hML : ∀ (P : Sd) (t : FvState Tw Msg), FvValid cap t →
      MarkLaw (rowEmb P) (fvC t) (fvSeen (Y := Y) t))
    (g : ℝ) (hg0 : 0 ≤ g)
    (hg : 2 * (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card Msg - 1) - 1 ≤ g) :
    dsprSuccHyb I ρ cap n x ph2 ≤ dsprSPHyb I ρ cap n x ph2 +
      ENNReal.ofReal (g + 168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) := by
  unfold dsprSuccHyb dsprSPHyb twoPhaseHyb
  refine avg_le_avg_add fun P ↦ avg_le_avg_add fun F ↦ ?_
  simp only [hybProb_eq_tsum hx, avg_tsum]
  refine (tsum_le_tsum fun p ↦ dspr_leaf_tight h2 P F p (hML P p.2.2) g hg0 hg).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_left]
  refine add_le_add le_rfl ((mul_le_mul' le_rfl ?_).trans (mul_one _).le)
  simp only [← avg_tsum]
  refine avg_le fun R ↦ ?_
  exact (tsum_leaf_le (R := twoRuntime fun _ ↦ F) (I := I)
    (phase1 (fvCh R) fvInit n x) (joint_posSemidef ρ)).trans (ofReal_trace_joint_le_one ρ)

/-- **SM-DT-DSPR (source final validity), exact adaptive two-phase game, tight and
target-count-free**: `Success − SPprob ≤ g + 168 q₂² / |Y| + 2 · seedLoss`, conditional on
`MarkLaw`. -/
theorem dspr_exact_adv_le_tight [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hML : ∀ (P : Sd) (t : FvState Tw Msg), FvValid cap t →
      MarkLaw (rowEmb P) (fvC t) (fvSeen (Y := Y) t))
    (g : ℝ) (hg0 : 0 ≤ g)
    (hg : 2 * (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card Msg - 1) - 1 ≤ g) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      ENNReal.ofReal (g + 168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) + 2 * seedLoss Sd q₁ :=
  (dspr_adv_le_hyb_add hx h2).trans
    (add_le_add (tsub_le_iff_left.2 (dsprSuccHyb_le_SPHyb_add_tight hx h2 hML g hg0 hg)) le_rfl)

/-- **`2 ≤ |Y| ≤ |Msg|`**: `Success − SPprob ≤ 168 q₂² / |Y| + 2 · seedLoss`. -/
theorem dspr_exact_adv_le_tight_of_card [Inhabited Tw] (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hML : ∀ (P : Sd) (t : FvState Tw Msg), FvValid cap t →
      MarkLaw (rowEmb P) (fvC t) (fvSeen (Y := Y) t)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      ENNReal.ofReal (168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) + 2 * seedLoss Sd q₁ := by
  have : Nonempty Msg := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have h := dspr_exact_adv_le_tight (I := I) (ρ := ρ) hx h2 hML 0 le_rfl
    (by have := Tight.pow_noSP_le_half' (X := Msg) (Y := Y) hY hcard; linarith)
  rwa [zero_add] at h

/-- **Classical first phase, `2 ≤ |Y| ≤ |Msg|`**: `Success − SPprob ≤ 168 q₂² / |Y|`. -/
theorem dspr_exact_adv_le_tight_zeroPre_of_card [Inhabited Tw] (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hML : ∀ (P : Sd) (t : FvState Tw Msg), FvValid cap t →
      MarkLaw (rowEmb P) (fvC t) (fvSeen (Y := Y) t)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      ENNReal.ofReal (168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) := by
  have h := dspr_exact_adv_le_tight_of_card (I := I) (ρ := ρ) hY hcard hx h2 hML
  rwa [seedLoss_zero, mul_zero, add_zero] at h

/-- The mark law holds at every valid final-validity state of the exact game. -/
theorem fv_markLaw (P : Sd) (t : FvState Tw Msg) (hv : FvValid cap t) :
    MarkLaw (rowEmb P) (fvC t) (fvSeen (Y := Y) t) :=
  markLaw_of_obs (rowEmb P) (fvC t) (fvSeen t)
    fun k m hc hk R v ↦ fvSeen_update cap t hv k m hc hk R v

/-- **SM-DT-DSPR (source final validity) in the QROM, exact adaptive two-phase game, tight and
target-count-free** (unconditional): for any `g ≥ max 0 (2γ − 1)`, `γ = (1 − 1/|Y|)^(|Msg| − 1)`,
`Success − SPprob ≤ g + 168 q₂² / |Y| + 2 · seedLoss Sd q₁`. -/
theorem dspr_exact_tight [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (g : ℝ) (hg0 : 0 ≤ g)
    (hg : 2 * (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card Msg - 1) - 1 ≤ g) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      ENNReal.ofReal (g + 168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) + 2 * seedLoss Sd q₁ :=
  dspr_exact_adv_le_tight hx h2 (fun P t hv ↦ fv_markLaw P t hv) g hg0 hg

/-- **`2 ≤ |Y| ≤ |Msg|`** (unconditional):
`Success − SPprob ≤ 168 q₂² / |Y| + 2 · seedLoss Sd q₁`. -/
theorem dspr_exact_tight_of_card [Inhabited Tw] (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      ENNReal.ofReal (168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) + 2 * seedLoss Sd q₁ :=
  dspr_exact_adv_le_tight_of_card hY hcard hx h2 (fun P t hv ↦ fv_markLaw P t hv)

/-- **Classical first phase, `2 ≤ |Y| ≤ |Msg|`** (unconditional):
`Success − SPprob ≤ 168 q₂² / |Y|`, with no dependence on the number of targets. -/
theorem dspr_exact_tight_zeroPre_of_card [Inhabited Tw] (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      ENNReal.ofReal (168 * (q₂ : ℝ) ^ 2 / Fintype.card Y) :=
  dspr_exact_adv_le_tight_zeroPre_of_card hY hcard hx h2 (fun P t hv ↦ fv_markLaw P t hv)

end Game

end PQ.QROM

#print axioms PQ.QROM.markLaw_of_obs
#print axioms PQ.QROM.dspr_exact_tight
#print axioms PQ.QROM.dspr_exact_tight_of_card
#print axioms PQ.QROM.dspr_exact_tight_zeroPre_of_card
