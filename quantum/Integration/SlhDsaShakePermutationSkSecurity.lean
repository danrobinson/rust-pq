import Integration.SlhDsaShakePermutationSkCompare
import Integration.SlhDsaShakePermutationColumnGame
import Integration.SlhDsaShakePermutationSkGames

namespace Reduction.ShakePermutation.SkGames
open Classical MLink SLHDSA SLHDSA.Security Quantum PQ.Interactive PQ.QROM ENNReal SetOracle
open scoped Kronecker ComplexOrder
set_option maxRecDepth 8192
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
variable (A : Machine S E) (ρ : SubState ((Port × Words) × E))

/-- The native SK.PRF game with coherent access to the same uniform
permutation in *both* directions. Classical PRF calls may be adaptive. -/
theorem real_le_ideal (q : ℕ) (hA : PrfAnswerCost A q) :
    uniformMean (fun π : Permutation => qPrfRealPr (skPrfC S.vp (primitives (lanes π) S.vp.params))
      (A (oracle π)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    uniformMean (fun π : Permutation => qPrfIdealPr (A (oracle π)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) +
      ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) + ((2:ℝ≥0∞)^55)⁻¹ := by
  rw [real_mean,ideal_mean,← Compression.node_card_real S]
  apply SkCompare.compare S (B S A ρ) (B_le_one S A ρ q hA)
  intro π w ok
  exact Program.column_game π (Program.labelled (SkFormat.input S) π (SkFormat.target S w) ok)
    (fun H => ansRun (fun d => w.1 (ShakeXof.skAddress S d)) (A H)) q (hA _) ρ

private theorem benchmark_loss :
    ENNReal.ofReal (8*((2^41 : ℕ):ℝ)^2 / 2^(8*S.vp.params.n)) + ((2:ℝ≥0∞)^55)⁻¹ ≤ ((2:ℝ≥0∞)^42)⁻¹ := by
  have n : 128 ≤ 8*S.vp.params.n := by cases S <;> decide
  have small : (2:ℝ)^128 ≤ 2^(8*S.vp.params.n) := pow_le_pow_right₀ (by norm_num) n
  have b := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity : 0 ≤ 8*((2^41 : ℕ):ℝ)^2) (by positivity) small)
  apply (add_le_add b (le_rfl : ((2:ℝ≥0∞)^55)⁻¹ ≤ _)).trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal]
  norm_num

/-- The numerical allowance includes a further 2^40 permutation queries
beyond the external signature benchmark. -/
theorem benchmark (hA : PrfAnswerCost A (2^41)) :
    uniformMean (fun π : Permutation => qPrfRealPr (skPrfC S.vp (primitives (lanes π) S.vp.params))
      (A (oracle π)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    uniformMean (fun π : Permutation => qPrfIdealPr (A (oracle π)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) +
      ((2:ℝ≥0∞)^42)⁻¹ := by
  exact (real_le_ideal S A ρ _ hA).trans (by rw [add_assoc]; exact add_le_add le_rfl (benchmark_loss S))

end Reduction.ShakePermutation.SkGames
#print axioms Reduction.ShakePermutation.SkGames.benchmark
