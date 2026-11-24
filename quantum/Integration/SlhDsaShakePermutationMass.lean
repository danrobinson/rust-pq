import Integration.SlhDsaShakePermutationGraph
import VCVio.Quantum.Oracle.Compressed.ProjectorEvent

/-! Accumulated bad-mask mass in a coherent computation. Operations on
the surrounding work registers and first-class quantum query selectors
are allowed between the two-mask oracle calls. -/
namespace Reduction.ShakePermutation.Tails
open Classical Quantum OracleSpec Matrix ENNReal
open scoped Matrix.Norms.L2Operator Kronecker

section
variable {R C E K : Type} [Fintype R] [Fintype C] [Fintype E] [Fintype K]
  [DecidableEq R] [DecidableEq C] [DecidableEq E] [DecidableEq K] [AddCommGroup C]

abbrev MaskWork (R C E : Type) := ((Tagged R × C) × Database (Tagged R) C) × E

noncomputable def badProjector (π : Layout R C) : Matrix (MaskWork R C E) (MaskWork R C E) ℂ :=
  labelProjector (fun m : (Tagged R × C) × Database (Tagged R) C => goodLabel π m.2) false ⊗ₖ
    (1 : Matrix E E ℂ)

/-- A selector-controlled, normalized (or subnormalized) query computation.
The extra contraction may act coherently on the selector and work registers. -/
structure MaskRun (π : Layout R C) (E K : Type) [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]
    (t q : Nat) where
  selection : Finset K
  state : Nat → MaskWork R C E × K → ℂ
  step : Nat → Matrix (MaskWork R C E × K) (MaskWork R C E × K) ℂ
  op : Nat → K → Matrix (MaskWork R C E) (MaskWork R C E) ℂ
  step_contraction : ∀ j < q, ‖step j‖ ≤ 1
  step_commute : ∀ j < q, step j * blockDiagonal (fun _ => badProjector π) =
    blockDiagonal (fun _ => badProjector π) * step j
  selected : ∀ j < q, ∀ k ∈ selection, op j k = truncatedOracle (Tagged R) C t ⊗ₖ (1 : Matrix E E ℂ)
  other_contraction : ∀ j < q, ∀ k ∉ selection, ‖op j k‖ ≤ 1
  other_commute : ∀ j < q, ∀ k ∉ selection, badProjector π * op j k = op j k * badProjector π
  run_eq : ∀ j < q, state (j+1) = step j *ᵥ (blockDiagonal (op j) *ᵥ state j)
  good_start : blockDiagonal (fun _ => badProjector π) *ᵥ state 0 = 0
  normalized : ∀ j < q, ∑ k ∈ selection, ∑ x, ‖state j (x,k)‖ ^ 2 ≤ 1

noncomputable def badMass (π : Layout R C) {t q : Nat} (a : MaskRun π E K t q) :=
  ∑ x, ‖(blockDiagonal (fun _ => badProjector π) *ᵥ a.state q) x‖ ^ 2

variable [UniformAnswerMeasure ((Tagged R) →ₒ C)]

theorem badMass_bound (π : Layout R C) {t q B : Nat} (a : MaskRun π E K t q)
    (h : Database.instability (goodLabel π) t ≤ (B : ℝ≥0∞) / Fintype.card C) :
    badMass π a ≤ 6 * (q:ℝ)^2 * B / Fintype.card C := by
  have hx := sum_norm_labelProjector_mulVec_sq_le_six_mul_mul_sum (goodLabel π) t false
    a.selection q a.state a.step a.op a.step_contraction a.step_commute a.selected
    a.other_contraction a.other_commute a.run_eq a.good_start
  have h' : (Fintype.card C : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h') h
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast] at hr
  have hsum : ∑ j ∈ Finset.range q, ∑ k ∈ a.selection, ∑ x, ‖a.state j (x,k)‖ ^ 2 ≤ (q:ℝ) := by
    apply le_trans (Finset.sum_le_sum fun j hj => a.normalized j (Finset.mem_range.mp hj))
    simp
  apply hx.trans
  calc _ ≤ 6 * q * ((B:ℝ) / Fintype.card C) * q := by gcongr
       _ = _ := by ring

end
end Reduction.ShakePermutation.Tails
#print axioms Reduction.ShakePermutation.Tails.badMass_bound
