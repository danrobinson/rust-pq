import PQ.QROM.Distinguish

/-!
# DSPR of a random function in the advantage form (Bernstein–Hülsing / VCVio)

VCVio's `TweakableHash.SM_DT_DSPR_SourceFinalValidity.advantage adv` is the truncated difference
`Success adv - SPProbability adv` (i.e. `max 0 (Pr[DSPR] − Pr[SPprob])`), where

* `Success` is the probability of `experiment`: the adversary selects targets `(t, m)` (distinct
  tweaks, seed withheld), then given the seed outputs an index `j` and a bit `b`, and wins iff the
  run is valid and `b` equals the truth value of "the `j`-th target has a second preimage";
* `SPProbability` is the probability of `spExperiment`: the SAME run (same adversary, same
  selected index), accepted iff the run is valid and the `j`-th target HAS a second preimage,
  whatever the bit.

This is the DSPR advantage of Bernstein–Hülsing (`max 0 (Pr[b = SP] − Pr[SP])`).

Here: the single-function, single-target, one-shot analogue.  `H : X → Y` uniform, the target
`x : X` uniform (so the baseline does not depend on the adversary), `SP = SecondPreimage H x`:

* `Success  := Pr[b ↔ SP]` (LHS of `dspr_le`),
* `SPprob   := Pr[SP] = spProb X Y = 1 − γ`, `γ = (1 − 1/|Y|)^(|X|−1)` (`dspr_spProb`),
* `dspr_advantage_le`: `Success − SPprob ≤ (γ − (1 − γ)) + 4 q / √|Y|` (truncated subtractions).

The first term `max 0 (2γ − 1) = max 0 (1 − 2·Pr[SP])` cannot be removed: the adversary that
always answers "no second preimage" has `Success = γ`, hence advantage `2γ − 1` when `γ > 1/2`
(a domain too small for second preimages to be likely).  It vanishes iff `Pr[SP] ≥ 1/2`
(`dspr_advantage_le_of_half`), which holds for compressing parameters (e.g. `|X| − 1 ≥ |Y|`
gives `γ ≤ 1/e`; this numeric fact is not proved here, the condition `γ ≤ 1 − γ` is a hypothesis
of `dspr_advantage_le_of_half`).

Not covered: VCVio's multi-target structure (adaptive selection of targets under distinct tweaks,
the collection oracle, the withheld seed, the validity monitor).
-/

open ENNReal Finset

universe u v w

namespace PQ.QROM

section

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

instance SecondPreimage.decidable (H : X → Y) (x : X) : Decidable (SecondPreimage H x) := by
  unfold SecondPreimage
  infer_instance

/-- The `SPprob` baseline: the probability that a uniform point has a second preimage under a
uniform function. -/
noncomputable def spProb (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    ℝ≥0∞ :=
  ∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
    (if SecondPreimage H x then (1 : ℝ≥0∞) else 0)

/-- **Exact value of the baseline.** -/
theorem dspr_spProb [Nonempty X] [Nontrivial Y] :
    spProb X Y = 1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) := by
  have hγ := dspr_prob_noSP (X := X) (Y := Y)
  have hγ1 : (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) ≤ 1 :=
    pow_le_one₀ zero_le tsub_le_self
  have hpt : ∀ (H : X → Y) (x : X),
      (if SecondPreimage H x then (1 : ℝ≥0∞) else 0) + noSPw H x = 1 := by
    intro H x
    by_cases h : SecondPreimage H x
    · simp [h, noSPw_of_SP h]
    · simp [h, noSPw_of_not_SP h]
  have hsum : spProb X Y + (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) = 1 := by
    rw [← hγ]
    unfold spProb
    simp only [← Finset.sum_add_distrib, ← mul_add, hpt, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    calc (Fintype.card (X → Y) : ℝ≥0∞) * ((Fintype.card X : ℝ≥0∞) *
          ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹))
        = ((Fintype.card (X → Y) : ℝ≥0∞) * (Fintype.card (X → Y) : ℝ≥0∞)⁻¹) *
            ((Fintype.card X : ℝ≥0∞) * (Fintype.card X : ℝ≥0∞)⁻¹) := by ring
      _ = 1 := by rw [card_mul_inv_cancel, card_mul_inv_cancel, one_mul]
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top hγ1) hsum

variable {Leaf : Type} {q : ℕ}

/-- **DSPR advantage of a random function (HybridModel level).**  `H ← (X → Y)` uniform, `x ← X`
uniform; the `q`-query algorithm `M x` outputs a bit `b x p`.  Its DSPR advantage
`Pr[b ↔ SP] − Pr[SP]` (truncated, as in VCVio's `SM_DT_DSPR_SourceFinalValidity.advantage`) is at
most `max 0 (2γ − 1) + 4 q / √|Y|`, `γ = (1 − 1/|Y|)^(|X|−1) = 1 − Pr[SP]`. -/
theorem dspr_advantage_le [Nonempty X] [Nontrivial Y] (M : X → HybridModel X Y Leaf q)
    (b : X → Leaf → Prop) :
    (∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x)) - spProb X Y ≤
      ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) -
          (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))) +
        4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rw [dspr_spProb]
  set γ : ℝ≥0∞ := (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) with hγ
  have hmax : max (1 - γ) γ - (1 - γ) = γ - (1 - γ) := by
    rcases le_total γ (1 - γ) with h | h
    · rw [max_eq_left h, tsub_self, tsub_eq_zero_of_le h]
    · rw [max_eq_right h]
  calc _ ≤ (max (1 - γ) γ + 4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) - (1 - γ) :=
        tsub_le_tsub_right (dspr_le M b) _
    _ ≤ (max (1 - γ) γ - (1 - γ)) + 4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
        add_tsub_le_tsub_add
    _ = _ := by rw [hmax]

/-- **DSPR advantage, likely-second-preimage regime.**  If `Pr[SP] ≥ 1/2` (`γ ≤ 1 − γ`), the
DSPR advantage is at most `4 q / √|Y|`. -/
theorem dspr_advantage_le_of_half [Nonempty X] [Nontrivial Y]
    (hhalf : (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) ≤
      1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))
    (M : X → HybridModel X Y Leaf q) (b : X → Leaf → Prop) :
    (∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x)) - spProb X Y ≤
      4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := dspr_advantage_le M b
  rwa [tsub_eq_zero_of_le hhalf, zero_add] at h

section Program

open Quantum

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **DSPR advantage, program level.** -/
theorem dspr_advantage_qprob_le [Nonempty X] [Nontrivial Y] (I : L.Interp)
    (x : X → QuantumComp L (qromSpec X Y) W A) (ρ : X → SubState A) (q : ℕ)
    (hx : ∀ k, QueryBounded (x k) q) (b : X → (Σ u, W u) → Prop) :
    (∑ H : X → Y, ∑ k : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)) - spProb X Y ≤
      ((1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) -
          (1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))) +
        4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  dspr_advantage_le (fun k ↦ HybridModel.ofProgram I (x k) (ρ k) q (hx k) (b k))
    fun _ leaf ↦ leaf

/-- **DSPR advantage, program level, likely-second-preimage regime.** -/
theorem dspr_advantage_qprob_le_of_half [Nonempty X] [Nontrivial Y]
    (hhalf : (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1) ≤
      1 - (1 - (Fintype.card Y : ℝ≥0∞)⁻¹) ^ (Fintype.card X - 1))
    (I : L.Interp) (x : X → QuantumComp L (qromSpec X Y) W A) (ρ : X → SubState A) (q : ℕ)
    (hx : ∀ k, QueryBounded (x k) q) (b : X → (Σ u, W u) → Prop) :
    (∑ H : X → Y, ∑ k : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)) - spProb X Y ≤
      4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  dspr_advantage_le_of_half hhalf
    (fun k ↦ HybridModel.ofProgram I (x k) (ρ k) q (hx k) (b k)) fun _ leaf ↦ leaf

end Program

end

end PQ.QROM

#print axioms PQ.QROM.dspr_spProb
#print axioms PQ.QROM.dspr_advantage_le
#print axioms PQ.QROM.dspr_advantage_le_of_half
#print axioms PQ.QROM.dspr_advantage_qprob_le
#print axioms PQ.QROM.dspr_advantage_qprob_le_of_half
