import PQ.QROM.TightInstances
import PQ.QROM.PurifyTight

/-!
# Tight (second-order) bounds for ALL VCVio programs: PRF, undetectability, DSPR

`PQ/QROM/PurifyTight.lean` proves the tight hidden-set bound `8 q² ε` for every VCVio program
(`qprob_tight_avg`).  Here the three instances of `PQ/QROM/TightInstances.lean` are re-proved for
an arbitrary real-valued functional `f` of the oracle function satisfying that bound
(`TightAvgBound f q`; `…_tight_of`), and instantiated with `qprob` of arbitrary programs:

* `prf_tight_program`: `|Pr_real - Pr_ideal| ≤ 8 q² / |K|`;
* `ud_tight_program`: `|Pr_real - Pr_ideal| ≤ 8 q² / |Msg|` (program, initial state and event may
  depend on the targets);
* `dspr_tight_program`: `Pr[b = SP] ≤ max (p, 1 - p) + 8 q² / |Y|` (program, initial state and
  bit decoding may depend on the challenge point); `dspr_tight_adv_program`: the
  Bernstein–Hülsing advantage `max (0, Pr[b = SP] - p) ≤ 8 q² / |Y|` for `|Y| < |X|`.

These are statements about exactly the objects of `PQ/QROM/Distinguish.lean`
(`prf_qprob_real_le_ideal_add`, `ud_qprob_real_le_ideal_add`, `dspr_qprob_le`): every
`QuantumComp L (qromSpec X Y) W A` with `QueryBounded x q`, any interpretation, any initial
substate, any leaf event; probabilities are read in `ℝ` (`ENNReal.toReal`; they are `≤ 1`).
-/

open Finset ENNReal Quantum

set_option linter.unusedSectionVars false

universe u v w

namespace PQ.QROM.Tight

/-- `f` satisfies the tight hidden-set bound with `q` queries. -/
def TightAvgBound {X Y : Type} [DecidableEq X] (f : (X → Y) → ℝ) (q : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (w : ι → ℝ), (∀ s, 0 ≤ w s) → ∀ (Hs : ι → X → Y) (G : X → Y)
    (S : ι → Finset X), (∀ s k, Hs s k ≠ G k → k ∈ S s) → ∀ ε : ℝ, 0 ≤ ε →
    (∀ k, ∑ s with k ∈ S s, w s ≤ ε) →
    |∑ s, w s * f (Hs s) - (∑ s, w s) * f G| ≤ 8 * (q : ℝ) ^ 2 * ε

/-- Circuits of the vector model satisfy the bound (`tight_avg`). -/
theorem QAlg.tightAvgBound {X Y : Type} [Fintype X] [DecidableEq X] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (I : OracleInterface X Y E) (A : QAlg E)
    (q : ℕ) (Q : E →L[ℂ] E) (hQ : ∀ φ, ‖Q φ‖ ≤ ‖φ‖) : TightAvgBound (A.acc I q Q) q :=
  fun _ _ w hw Hs G S hS ε hε0 hε ↦ tight_avg I A w hw Hs G S hS ε hε0 hε q Q hQ

/-- **Every VCVio program satisfies the bound** (`qprob_tight_avg`). -/
theorem qprob_tightAvgBound {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg} (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q)
    (E : (Σ u, W u) → Prop) : TightAvgBound (fun H ↦ (qprob I H x ρ E).toReal) q :=
  fun _ _ w hw Hs G S hS ε hε0 hε ↦
    Purify.qprob_tight_avg I x ρ q hx E w hw Hs G S hS ε hε0 hε

section View

variable {X Y : Type} [DecidableEq X] {Ω V : Type} [Fintype Ω] [Fintype V] [DecidableEq V]

/-- `tight_view` for an arbitrary family of functionals satisfying the tight bound. -/
theorem tight_view_of (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω)
    (hc1 : ∀ ω, c ω ≤ 1) (view : Ω → V) (S : Ω → Finset X) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hH : ∀ v k, ∑ ω with view ω = v ∧ k ∈ S ω, w ω ≤ ε * ∑ ω with view ω = v, w ω)
    (q : ℕ) (f : V → (X → Y) → ℝ) (hf : ∀ v, TightAvgBound (f v) q)
    (Hreal : Ω → X → Y) (Ghyb : V → X → Y)
    (hS : ∀ ω k, Hreal ω k ≠ Ghyb (view ω) k → k ∈ S ω) :
    |∑ ω, w ω * c ω * f (view ω) (Hreal ω) -
        ∑ ω, w ω * c ω * f (view ω) (Ghyb (view ω))| ≤
      8 * (q : ℝ) ^ 2 * ε * ∑ ω, w ω := by
  classical
  have key : ∀ f : Ω → V → ℝ, ∑ ω, f ω (view ω) = ∑ v, ∑ ω, if view ω = v then f ω v else 0 := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp
  have hv : ∀ v, |(∑ ω, if view ω = v then w ω * c ω * f v (Hreal ω) else 0) -
      ∑ ω, if view ω = v then w ω * c ω * f v (Ghyb v) else 0| ≤
      8 * (q : ℝ) ^ 2 * (ε * ∑ ω with view ω = v, w ω) := by
    intro v
    have hμ : 0 ≤ ∑ ω with view ω = v, w ω := Finset.sum_nonneg fun ω _ ↦ hw ω
    have h := hf v Ω (fun ω ↦ if view ω = v then w ω * c ω else 0)
      (fun ω ↦ by split_ifs <;> [exact mul_nonneg (hw ω) (hc0 ω); exact le_rfl])
      (fun ω ↦ if view ω = v then Hreal ω else Ghyb v) (Ghyb v) S
      (fun ω k hne ↦ by
        by_cases hω : view ω = v
        · simp only [hω, ite_true] at hne
          exact hS ω k (by rw [hω]; exact hne)
        · simp [hω] at hne)
      (ε * ∑ ω with view ω = v, w ω) (mul_nonneg hε0 hμ)
      (fun k ↦ by
        refine le_trans ?_ (hH v k)
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_le_sum fun ω _ ↦ ?_
        by_cases h1 : view ω = v <;> by_cases h2 : k ∈ S ω <;> simp [h1, h2]
        nlinarith [hw ω, hc0 ω, hc1 ω])
    have e1 : ∑ ω, (if view ω = v then w ω * c ω else 0) *
        f v (if view ω = v then Hreal ω else Ghyb v) =
        ∑ ω, if view ω = v then w ω * c ω * f v (Hreal ω) else 0 :=
      Finset.sum_congr rfl fun ω _ ↦ by split_ifs <;> simp
    have e2 : (∑ ω, if view ω = v then w ω * c ω else 0) * f v (Ghyb v) =
        ∑ ω, if view ω = v then w ω * c ω * f v (Ghyb v) else 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ω _ ↦ by split_ifs <;> simp
    rw [e1, e2] at h
    exact h
  rw [key fun ω v ↦ w ω * c ω * f v (Hreal ω),
    key fun ω v ↦ w ω * c ω * f v (Ghyb v), ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun v _ ↦ hv v).trans ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_fiberwise]
  exact le_of_eq (by ring)

end View

section PRF

variable {K D Y : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D] [Fintype Y]
  [DecidableEq Y]

/-- Tight PRF bound for any functional satisfying the tight hidden-set bound. -/
theorem prf_tight_of [Nonempty K] [Nonempty D] [Nonempty Y] (q : ℕ)
    (f : ((K × D) ⊕ D → Y) → ℝ) (hf : TightAvgBound f q) :
    |∑ k : K, ∑ F : K × D → Y,
          ((Fintype.card K : ℝ)⁻¹ * (Fintype.card (K × D → Y) : ℝ)⁻¹) *
            f (prfReal k F) -
        ∑ F : K × D → Y, ∑ R : D → Y,
          ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹) *
            f (prfIdeal F R)| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card K := by
  obtain ⟨e1, e2, e3⟩ := prf_coupling_real (K := K) (D := D) (Y := Y) f
  have hκ : (0 : ℝ) ≤ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
      (Fintype.card (D → Y) : ℝ)⁻¹) := by positivity
  have hid : ∀ x : (K × D) ⊕ D, ∑ k : K, (if x ∈ prfMarked (D := D) k then (1 : ℝ) else 0) ≤
      (Fintype.card K : ℝ)⁻¹ * Fintype.card K := by
    intro x
    rw [inv_mul_cancel₀ (card_ne_zero_real K)]
    rcases x with ⟨k', d⟩ | d
    · have hm : ∀ k : K, (Sum.inl (k', d) ∈ prfMarked (D := D) k) ↔ k = k' := by
        intro k
        simp only [prfMarked, Finset.mem_image, Finset.mem_univ, true_and, Sum.inl.injEq,
          Prod.mk.injEq]
        constructor
        · rintro ⟨_, h, _⟩
          exact h
        · intro h
          exact ⟨d, h, rfl⟩
      simp [hm]
    · have hm : ∀ k : K, ¬ (Sum.inr d ∈ prfMarked (D := D) k) := by
        intro k
        simp [prfMarked]
      simp [hm]
  have h := tight_view_of (Ω := K × ((K × D → Y) × (D → Y)))
    (fun _ ↦ (Fintype.card K : ℝ)⁻¹ * ((Fintype.card (K × D → Y) : ℝ)⁻¹ *
      (Fintype.card (D → Y) : ℝ)⁻¹)) (fun _ ↦ hκ) (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (fun _ ↦ le_rfl) (fun ω ↦ ω.2) (fun ω ↦ prfMarked (D := D) ω.1) (Fintype.card K : ℝ)⁻¹
    (by positivity) (hidden_indep_real _ _ hκ _ hid) q (fun _ ↦ f) (fun _ ↦ hf)
    (fun ω ↦ prfReal ω.1 (prfSwapRow ω.1 ω.2.1 ω.2.2)) (fun v ↦ prfIdeal v.1 v.2) prf_differ
  simp only [mul_one] at h
  rw [e1, e2, e3] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end PRF

section UD

variable {T Msg Y : Type} [Fintype T] [DecidableEq T] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y]

/-- Tight multi-target undetectability for any family of functionals satisfying the tight
hidden-set bound. -/
theorem ud_tight_of [Nonempty T] [Nonempty Msg] [Nonempty Y] (q : ℕ)
    (f : (T → Y) → (T × Msg → Y) → ℝ) (hf : ∀ y, TightAvgBound (f y) q) :
    |∑ xs : T → Msg, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Msg) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            f (udTargets xs H) H -
        ∑ y : T → Y, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Y) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            f y H| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card Msg := by
  obtain ⟨e1, e2, e3⟩ := ud_coupling_real (T := T) (Msg := Msg) (Y := Y)
    fun y H ↦ f y H
  have hκ : (0 : ℝ) ≤ (Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
      (Fintype.card (T × Msg → Y) : ℝ)⁻¹) := by positivity
  have h := tight_view_of (Ω := (T → Msg) × ((T → Y) × (T × Msg → Y)))
    (fun _ ↦ (Fintype.card (T → Msg) : ℝ)⁻¹ * ((Fintype.card (T → Y) : ℝ)⁻¹ *
      (Fintype.card (T × Msg → Y) : ℝ)⁻¹)) (fun _ ↦ hκ) (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    (fun _ ↦ le_rfl) (fun ω ↦ ω.2) (fun ω ↦ udMarked ω.1) (Fintype.card Msg : ℝ)⁻¹
    (by positivity) (hidden_indep_real _ _ hκ _ fun p ↦ le_of_eq (sum_udMarked_real p))
    q (fun v ↦ f v.1) (fun v ↦ hf v.1)
    (fun ω ↦ udReprog ω.1 ω.2.1 ω.2.2) (fun v ↦ v.2) ud_differ
  simp only [mul_one] at h
  rw [e1, e2, e3] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end UD

section DSPR

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

open Classical in
/-- Tight DSPR for any pair of functionals `f₁` ("answers SP"), `f₀` ("answers no SP") with
`f₁ + f₀ ≤ 1`, `f₁` satisfying the tight hidden-set bound. -/
theorem dspr_tight_of (q : ℕ) (f₁ f₀ : X → (X → Y) → ℝ) (hf : ∀ x, TightAvgBound (f₁ x) q)
    (h₁ : ∀ x H, 0 ≤ f₁ x H) (h₀ : ∀ x H, 0 ≤ f₀ x H) (hsum : ∀ x H, f₁ x H + f₀ x H ≤ 1) :
    ∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (if SecondPreimage H x then f₁ x H else f₀ x H) ≤
      max (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))
          ((1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1)) +
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  have hcY : (1 : ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos (α := Y)
  have hinv0 : (0 : ℝ) ≤ (Fintype.card Y : ℝ)⁻¹ := by positivity
  have hinv1 : (Fintype.card Y : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcY
  set γ : ℝ := (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1) with hγdef
  have hγ0 : 0 ≤ γ := pow_nonneg (by linarith) _
  have hγ1 : γ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hδ : (0 : ℝ) ≤ 8 * (q : ℝ) ^ 2 / Fintype.card Y := by positivity
  have hmax0 : 0 ≤ max (1 - γ) γ := hγ0.trans (le_max_right _ _)
  rcases isEmpty_or_nonempty X with hX | hX
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
    positivity
  have hle1 : ∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
      (if SecondPreimage H x then f₁ x H else f₀ x H) ≤ 1 := by
    calc _ ≤ ∑ _H : X → Y, ∑ _x : X,
          ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) * 1 := by
          refine Finset.sum_le_sum fun H _ ↦ Finset.sum_le_sum fun x _ ↦
            mul_le_mul_of_nonneg_left ?_ (by positivity)
          split_ifs
          · linarith [hsum x H, h₀ x H]
          · linarith [hsum x H, h₁ x H]
      _ = 1 := by
          have iX := card_ne_zero_real X
          have iXY := card_ne_zero_real (X → Y)
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          field_simp
  by_cases hYnt : Nontrivial Y
  swap
  · have hY1 : Fintype.card Y = 1 := by
      have h1 := Fintype.card_pos (α := Y)
      have h2 : ¬ 1 < Fintype.card Y := fun h ↦ hYnt (Fintype.one_lt_card_iff_nontrivial.1 h)
      omega
    have hγ : γ = 0 ∨ γ = 1 := by
      rw [hγdef, hY1]
      rcases Nat.eq_zero_or_pos (Fintype.card X - 1) with h0 | h0
      · right; simp [h0]
      · left; simp [h0.ne']
    have : max (1 - γ) γ = 1 := by rcases hγ with h | h <;> simp [h]
    rw [this]
    linarith
  -- main case
  obtain ⟨e1, e2⟩ := dspr_coupling_real (X := X) (Y := Y)
    fun x H ↦ if SecondPreimage H x then f₁ x H else f₀ x H
  set κ : ℝ := (Fintype.card X : ℝ)⁻¹ * (Fintype.card (X → Y) : ℝ)⁻¹ *
          (Fintype.card (X → NZ Y) : ℝ)⁻¹ with hκdef
  have hκ : 0 ≤ κ := by positivity
  rw [← e1]
  let nsp : X × (X → Y × NZ Y) → ℝ := fun ω ↦ noSPr (fun k ↦ (ω.2 k).1) ω.1
  let a₁ : X × (X → Y × NZ Y) → ℝ := fun ω ↦ f₁ ω.1 (fun k ↦ (ω.2 k).1)
  let P1 : X × (X → Y) → ℝ := fun v ↦ f₁ v.1 v.2
  let P0 : X × (X → Y) → ℝ := fun v ↦ f₀ v.1 v.2
  have hterm : ∀ ω : X × (X → Y × NZ Y),
      κ * (if SecondPreimage (fun k ↦ (ω.2 k).1) ω.1 then
          f₁ ω.1 (fun k ↦ (ω.2 k).1)
        else f₀ ω.1 (fun k ↦ (ω.2 k).1)) =
      κ * (1 - nsp ω) * a₁ ω + nsp ω * (κ * P0 (ω.1, dsprHyb ω.1 ω.2)) := by
    intro ω
    by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
    · simp only [nsp, a₁, noSPr_of_SP hsp, hsp, ↓reduceIte]
      ring
    · have hfun : (fun k ↦ (ω.2 k).1) = dsprHyb ω.1 ω.2 := by
        funext k
        by_contra hne
        have hk := dspr_differ ω k hne
        simp only [dsprMarked, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hsp ⟨k, hk.1, hk.2⟩
      simp only [nsp, P0, noSPr_of_not_SP hsp, hsp, ↓reduceIte]
      rw [hfun]
      ring
  have tv := tight_view_of (Ω := X × (X → Y × NZ Y)) (fun _ ↦ κ) (fun _ ↦ hκ)
    (fun ω ↦ 1 - nsp ω)
    (fun ω ↦ by
      by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
      · simp [nsp, noSPr_of_SP hsp]
      · simp [nsp, noSPr_of_not_SP hsp])
    (fun ω ↦ by
      by_cases hsp : SecondPreimage (fun k ↦ (ω.2 k).1) ω.1
      · simp [nsp, noSPr_of_SP hsp]
      · simp [nsp, noSPr_of_not_SP hsp])
    (fun ω ↦ (ω.1, dsprHyb ω.1 ω.2)) dsprMarked (Fintype.card Y : ℝ)⁻¹ hinv0
    (dspr_hidden_real κ hκ) q (fun v ↦ f₁ v.1) (fun v ↦ hf v.1)
    (fun ω k ↦ (ω.2 k).1) (fun v ↦ v.2) dspr_differ
  rw [e2] at tv
  have i1 := dspr_noSP_indep_real κ hκ P1 fun v ↦ h₁ v.1 v.2
  have i0 := dspr_noSP_indep_real κ hκ P0 fun v ↦ h₀ v.1 v.2
  set A1 : ℝ := ∑ ω : X × (X → Y × NZ Y), κ * P1 (ω.1, dsprHyb ω.1 ω.2) with hA1
  set A0 : ℝ := ∑ ω : X × (X → Y × NZ Y), κ * P0 (ω.1, dsprHyb ω.1 ω.2) with hA0
  have hA1nn : 0 ≤ A1 := Finset.sum_nonneg fun ω _ ↦ mul_nonneg hκ (h₁ _ _)
  have hA0nn : 0 ≤ A0 := Finset.sum_nonneg fun ω _ ↦ mul_nonneg hκ (h₀ _ _)
  have hA : A1 + A0 ≤ 1 := by
    rw [hA1, hA0, ← Finset.sum_add_distrib, ← e2]
    refine Finset.sum_le_sum fun ω _ ↦ ?_
    rw [← mul_add]
    have := hsum ω.1 (dsprHyb ω.1 ω.2)
    calc κ * (P1 (ω.1, dsprHyb ω.1 ω.2) + P0 (ω.1, dsprHyb ω.1 ω.2)) ≤ κ * 1 :=
          mul_le_mul_of_nonneg_left this hκ
      _ = κ := mul_one _
  have hhyb : ∑ ω : X × (X → Y × NZ Y), κ * (1 - nsp ω) * P1 (ω.1, dsprHyb ω.1 ω.2) =
      A1 - γ * A1 := by
    rw [← i1, hA1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ by simp only [nsp]; ring
  have hsum : ∑ ω : X × (X → Y × NZ Y),
      κ * (if SecondPreimage (fun k ↦ (ω.2 k).1) ω.1 then
          f₁ ω.1 (fun k ↦ (ω.2 k).1)
        else f₀ ω.1 (fun k ↦ (ω.2 k).1)) =
      ∑ ω : X × (X → Y × NZ Y), κ * (1 - nsp ω) * a₁ ω + γ * A0 := by
    rw [← i0, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ hterm ω
  rw [hsum]
  have tv' := (abs_le.1 tv).2
  have htv : ∑ ω : X × (X → Y × NZ Y), κ * (1 - nsp ω) * a₁ ω ≤
      (A1 - γ * A1) + 8 * (q : ℝ) ^ 2 / Fintype.card Y := by
    rw [← hhyb]
    have e : 8 * (q : ℝ) ^ 2 * (Fintype.card Y : ℝ)⁻¹ * 1 = 8 * (q : ℝ) ^ 2 / Fintype.card Y := by
      ring
    rw [e] at tv'
    linarith
  have hfin : (1 - γ) * A1 + γ * A0 ≤ max (1 - γ) γ :=
    calc (1 - γ) * A1 + γ * A0 ≤ max (1 - γ) γ * A1 + max (1 - γ) γ * A0 :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA1nn)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0nn)
      _ = max (1 - γ) γ * (A1 + A0) := by ring
      _ ≤ max (1 - γ) γ * 1 := mul_le_mul_of_nonneg_left hA hmax0
      _ = _ := mul_one _
  linarith

end DSPR

/-! ## The tight bounds for arbitrary programs -/

section Programs

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Tight PRF security against every quantum query program.**  Same experiment and adversary
class as `prf_qprob_real_le_ideal_add`: any VCVio program with at most `q` calls to the folded
oracle on `(K × D) ⊕ D`, any interpretation, initial substate and leaf event.  The real and ideal
probabilities differ by at most `8 q² / |K|`. -/
theorem prf_tight_program {K D Y : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty K] [Nonempty D] (I : L.Interp)
    (x : QuantumComp L (qromSpec ((K × D) ⊕ D) Y) W A) (ρ : SubState A) (q : ℕ)
    (hx : QueryBounded x q) (E : (Σ u, W u) → Prop) :
    |∑ k : K, ∑ F : K × D → Y,
          ((Fintype.card K : ℝ)⁻¹ * (Fintype.card (K × D → Y) : ℝ)⁻¹) *
            (qprob I (prfReal k F) x ρ E).toReal -
        ∑ F : K × D → Y, ∑ R : D → Y,
          ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹) *
            (qprob I (prfIdeal F R) x ρ E).toReal| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card K :=
  prf_tight_of q (fun H ↦ (qprob I H x ρ E).toReal) (qprob_tightAvgBound I x ρ q hx E)

/-- **Tight multi-target undetectability against every quantum query program.**  Same
experiment and adversary class as `ud_qprob_real_le_ideal_add`: the program `x y`, its initial
state `ρ y` and the event `E y` may depend on the targets `y`.  The real and ideal probabilities
differ by at most `8 q² / |Msg|`, independently of the number of tweaks. -/
theorem ud_tight_program {T Msg Y : Type} [Fintype T] [DecidableEq T] [Fintype Msg]
    [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty T] [Nonempty Msg]
    (I : L.Interp) (x : (T → Y) → QuantumComp L (qromSpec (T × Msg) Y) W A)
    (ρ : (T → Y) → SubState A) (q : ℕ) (hx : ∀ y, QueryBounded (x y) q)
    (E : (T → Y) → (Σ u, W u) → Prop) :
    |∑ xs : T → Msg, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Msg) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            (qprob I H (x (udTargets xs H)) (ρ (udTargets xs H)) (E (udTargets xs H))).toReal -
        ∑ y : T → Y, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Y) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            (qprob I H (x y) (ρ y) (E y)).toReal| ≤ 8 * (q : ℝ) ^ 2 / Fintype.card Msg :=
  ud_tight_of q (fun y H ↦ (qprob I H (x y) (ρ y) (E y)).toReal)
    fun y ↦ qprob_tightAvgBound I (x y) (ρ y) q (hx y) (E y)

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **Tight decisional second-preimage resistance against every quantum query program.**  Same
experiment and adversary class as `dspr_qprob_le`: the program `x k`, its initial state `ρ k` and
the bit decoding `b k` may depend on the challenge point `k`; the program wins iff its bit says
correctly whether `k` has a second preimage.  The winning probability is at most
`max (p, 1 - p) + 8 q² / |Y|`, `1 - p = (1 - 1/|Y|)^(|X|-1)`. -/
theorem dspr_tight_program (I : L.Interp) (x : X → QuantumComp L (qromSpec X Y) W A)
    (ρ : X → SubState A) (q : ℕ) (hx : ∀ k, QueryBounded (x k) q)
    (b : X → (Σ u, W u) → Prop) :
    ∑ H : X → Y, ∑ k : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)).toReal ≤
      max (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))
          ((1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1)) +
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  classical
  have e : ∀ (H : X → Y) (k : X),
      (qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)).toReal =
      if SecondPreimage H k then (qprob I H (x k) (ρ k) (b k)).toReal
      else (qprob I H (x k) (ρ k) (fun p ↦ ¬ b k p)).toReal := by
    intro H k
    by_cases hsp : SecondPreimage H k
    · simp [hsp]
    · simp [hsp]
  simp only [e]
  exact dspr_tight_of q (fun k H ↦ (qprob I H (x k) (ρ k) (b k)).toReal)
    (fun k H ↦ (qprob I H (x k) (ρ k) (fun p ↦ ¬ b k p)).toReal)
    (fun k ↦ qprob_tightAvgBound I (x k) (ρ k) q (hx k) (b k))
    (fun _ _ ↦ ENNReal.toReal_nonneg) (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun k H ↦ Purify.qprob_toReal_add_not_le_one I H (x k) (ρ k) (b k))

/-- **Tight DSPR against every quantum query program, Bernstein–Hülsing advantage form.**  If
`|Y| < |X|` (so that `p = Pr[SP] ≥ 1/2`), the DSPR advantage `max (0, Pr[b = SP] - p)` of every
`q`-query program is at most `8 q² / |Y|`. -/
theorem dspr_tight_adv_program (I : L.Interp) (x : X → QuantumComp L (qromSpec X Y) W A)
    (ρ : X → SubState A) (q : ℕ) (hx : ∀ k, QueryBounded (x k) q)
    (b : X → (Σ u, W u) → Prop) (hcard : Fintype.card Y < Fintype.card X) :
    max 0 (∑ H : X → Y, ∑ k : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)).toReal -
      (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))) ≤
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  have h := dspr_tight_program I x ρ q hx b
  have hp := pow_noSP_le_half (X := X) (Y := Y) hcard
  rw [max_eq_left (by linarith)] at h
  refine max_le (by positivity) ?_
  linarith

/-- **Tight DSPR against every quantum query program, advantage form, `2 ≤ |Y| ≤ |X|`**
(equality `|X| = |Y|` allowed): the DSPR advantage `max (0, Pr[b = SP] - p)` of every `q`-query
program is at most `8 q² / |Y|`. -/
theorem dspr_tight_adv_program_of_card_le (I : L.Interp)
    (x : X → QuantumComp L (qromSpec X Y) W A) (ρ : X → SubState A) (q : ℕ)
    (hx : ∀ k, QueryBounded (x k) q) (b : X → (Σ u, W u) → Prop)
    (hY : 2 ≤ Fintype.card Y) (hXY : Fintype.card Y ≤ Fintype.card X) :
    max 0 (∑ H : X → Y, ∑ k : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)).toReal -
      (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))) ≤
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  have h := dspr_tight_program I x ρ q hx b
  have hp := pow_noSP_le_half' (X := X) (Y := Y) hY hXY
  rw [max_eq_left (by linarith)] at h
  refine max_le (by positivity) ?_
  linarith

end Programs

end PQ.QROM.Tight

#print axioms PQ.QROM.Tight.qprob_tightAvgBound
#print axioms PQ.QROM.Tight.prf_tight_program
#print axioms PQ.QROM.Tight.ud_tight_program
#print axioms PQ.QROM.Tight.dspr_tight_program
#print axioms PQ.QROM.Tight.dspr_tight_adv_program
#print axioms PQ.QROM.Tight.dspr_tight_adv_program_of_card_le
