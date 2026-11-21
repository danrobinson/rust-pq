import PQ.QROM.ExactDsprClosed
import PQ.QROM.DsprAdv

/-!
# DSPR: the trivial term vanishes for `2 ≤ |Y| ≤ |Msg|`

`(1 − 1/N)^(N−1) ≤ 1/2` for `N ≥ 2` (Bernoulli: `(1 + 1/(N−1))^(N−1) ≥ 2`).  Hence a point has no
second preimage with probability at most `1/2` as soon as the domain (the row of a tweak) is at
least as large as the range, and the trivial term `max 0 (2γ − 1)` of the DSPR bounds vanishes.
In particular this covers `Msg = Y`.

* `one_sub_inv_pow_pred_le_half`: the numeric fact.
* `dsprTrivial_eq_zero'`, `dspr_exact_adv_le_of_card'`: the exact two-phase SM-DT-DSPR game,
  `Success − SPprob ≤ 8 q₂ / √|Y| + 2 · seedLoss Sd q₁` for `2 ≤ |Y| ≤ |Msg|`.
* `dspr_advantage_le_of_card`, `dspr_advantage_qprob_le_of_card`: the one-shot single-function
  game of `PQ/QROM/DsprAdv.lean`, advantage at most `4 q / √|Y|` for `2 ≤ |Y| ≤ |X|`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

/-- `(1 - 1/(M+1))^M ≤ 1/2` for `M ≥ 1`, over the reals. -/
theorem real_one_sub_inv_succ_pow_le_half (M : ℕ) (hM : 1 ≤ M) :
    (1 - ((M + 1 : ℕ) : ℝ)⁻¹) ^ M ≤ 2⁻¹ := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ (M : ℝ)⁻¹ by
    have := inv_pos.2 hM'; linarith) M
  have h2 : (2 : ℝ) ≤ (1 + (M : ℝ)⁻¹) ^ M := by
    have : (M : ℝ) * (M : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hM'.ne'
    linarith
  have hx : 1 - ((M + 1 : ℕ) : ℝ)⁻¹ = (1 + (M : ℝ)⁻¹)⁻¹ := by
    push_cast
    field_simp
    ring
  rw [hx, inv_pow]
  exact inv_anti₀ (by norm_num) h2

/-- `(1 - 1/N)^k ≤ 1/2` for `N ≥ 2` and `k ≥ N - 1`. -/
theorem one_sub_inv_pow_pred_le_half (N k : ℕ) (hN : 2 ≤ N) (hk : N - 1 ≤ k) :
    (1 - (N : ℝ≥0∞)⁻¹) ^ k ≤ 2⁻¹ := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 1 ≤ M := by omega
  have hN' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos M
  have hinv1 : (((M + 1 : ℕ) : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M))
  have h0 : (0 : ℝ) ≤ 1 - (((M + 1 : ℕ) : ℝ))⁻¹ := by linarith
  have hconv : (1 : ℝ≥0∞) - (((M + 1 : ℕ) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (1 - (((M + 1 : ℕ) : ℝ))⁻¹) := by
    rw [ENNReal.ofReal_sub _ (inv_nonneg.2 hN'.le), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos hN', ENNReal.ofReal_natCast]
  calc (1 - (((M + 1 : ℕ) : ℝ≥0∞))⁻¹) ^ k
      ≤ (1 - (((M + 1 : ℕ) : ℝ≥0∞))⁻¹) ^ M :=
        pow_le_pow_of_le_one zero_le tsub_le_self (by omega)
    _ = ENNReal.ofReal ((1 - (((M + 1 : ℕ) : ℝ))⁻¹) ^ M) := by
        rw [hconv, ENNReal.ofReal_pow h0]
    _ ≤ ENNReal.ofReal 2⁻¹ :=
        ENNReal.ofReal_le_ofReal (real_one_sub_inv_succ_pow_le_half M hM)
    _ = 2⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp

/-- `γ ≤ 1 − γ` for `γ = (1 − 1/N)^k`, `N ≥ 2`, `k ≥ N − 1`. -/
theorem pow_noSP_le_one_sub (N k : ℕ) (hN : 2 ≤ N) (hk : N - 1 ≤ k) :
    (1 - (N : ℝ≥0∞)⁻¹) ^ k ≤ 1 - (1 - (N : ℝ≥0∞)⁻¹) ^ k := by
  have h := one_sub_inv_pow_pred_le_half N k hN hk
  refine h.trans ?_
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ _ := tsub_le_tsub_left h 1

/-! ## The exact two-phase game -/

section Exact

variable {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Bool) u}

/-- The trivial term vanishes as soon as `2 ≤ |Y| ≤ |Msg|` (in particular for `Msg = Y`). -/
theorem dsprTrivial_eq_zero' (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card Msg) : dsprTrivial Msg Y = 0 := by
  unfold dsprTrivial
  exact tsub_eq_zero_of_le (pow_noSP_le_one_sub _ _ hY (by omega))

/-- **SM-DT-DSPR in the QROM, exact game, `2 ≤ |Y| ≤ |Msg|`**:
`Success − SPprob ≤ 8 q₂ / √|Y| + 2 · (4 q₁ / √|Sd|)`. -/
theorem dspr_exact_adv_le_of_card' [Inhabited Tw] (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) + 2 * seedLoss Sd q₁ := by
  have : Nonempty Msg := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have h := dspr_exact_adv_le (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [dsprTrivial_eq_zero' hY hcard, zero_add] at h

end Exact

/-! ## The one-shot single-function game -/

section OneShot

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Leaf : Type} {q : ℕ}

/-- **DSPR advantage of a random function, `2 ≤ |Y| ≤ |X|`** (HybridModel level): the advantage
`Pr[b ↔ SP] − Pr[SP]` is at most `4 q / √|Y|`. -/
theorem dspr_advantage_le_of_card (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card X)
    (M : X → HybridModel X Y Leaf q) (b : X → Leaf → Prop) :
    (∑ H : X → Y, ∑ x : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          (M x).prob H (fun p ↦ b x p ↔ SecondPreimage H x)) - spProb X Y ≤
      4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  exact dspr_advantage_le_of_half (pow_noSP_le_one_sub _ _ hY (by omega)) M b

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **DSPR advantage, program level, `2 ≤ |Y| ≤ |X|`.** -/
theorem dspr_advantage_qprob_le_of_card (hY : 2 ≤ Fintype.card Y)
    (hcard : Fintype.card Y ≤ Fintype.card X) (I : L.Interp)
    (x : X → QuantumComp L (qromSpec X Y) W A) (ρ : X → SubState A) (q : ℕ)
    (hx : ∀ k, QueryBounded (x k) q) (b : X → (Σ u, W u) → Prop) :
    (∑ H : X → Y, ∑ k : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          qprob I H (x k) (ρ k) (fun p ↦ b k p ↔ SecondPreimage H k)) - spProb X Y ≤
      4 * q * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  exact dspr_advantage_qprob_le_of_half (pow_noSP_le_one_sub _ _ hY (by omega)) I x ρ q hx b

end OneShot

end PQ.QROM

#print axioms PQ.QROM.one_sub_inv_pow_pred_le_half
#print axioms PQ.QROM.dsprTrivial_eq_zero'
#print axioms PQ.QROM.dspr_exact_adv_le_of_card'
#print axioms PQ.QROM.dspr_advantage_le_of_card
#print axioms PQ.QROM.dspr_advantage_qprob_le_of_card
