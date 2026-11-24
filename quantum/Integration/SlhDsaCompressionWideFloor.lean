import Integration.SlhDsaCompressionWideClosed
import MReduction.Resources
namespace Reduction.Compression
open MLink Ideal SLHDSA ENNReal
variable (S : Sha2Set)

/-- Charging the entire classical honest walk as quantum queries in the
generic collision bound makes even the arity-two term vacuous at every budget. -/
theorem class_two_floor (hw : S.vp.params.n ≠ 16) (L q qs : ℕ) :
    1 ≤ 16*((classQueries S L q qs 2:ℝ≥0∞)+1)^3 / 2^(8*S.vp.params.n) := by
  let T := tcrTargets S.vp * ClassCollision.walkMax S
  have num : 2^(8*S.vp.params.n) ≤ 16*T^3 := by
    unfold T
    cases S <;> first | exact (hw rfl).elim | (
      rw [MReduction.tcrTargets_192s_val] <;> decide +kernel) | (
      rw [MReduction.tcrTargets_192f_val] <;> decide +kernel) | (
      rw [MReduction.tcrTargets_256s_val] <;> decide +kernel) | (
      rw [MReduction.tcrTargets_256f_val] <;> decide +kernel)
  have le : T ≤ classQueries S L q qs 2 := by unfold T classQueries; omega
  have inc : (T:ℝ≥0∞) ≤ (classQueries S L q qs 2:ℝ≥0∞)+1 :=
    (Nat.cast_le.mpr le).trans le_self_add
  have a : (2:ℝ≥0∞)^(8*S.vp.params.n) ≤ 16*(T:ℝ≥0∞)^3 := by exact_mod_cast num
  let d : ℝ≥0∞ := 2^(8*S.vp.params.n)
  have h₁ : d ≠ 0 := by dsimp [d]; positivity
  have h₂ : d ≠ ⊤ := by dsimp [d]; finiteness
  change 1 ≤ _ / d
  rw [div_eq_mul_inv]
  apply le_trans (le_of_eq (ENNReal.mul_inv_cancel h₁ h₂).symm)
  exact mul_le_mul' (a.trans (mul_le_mul' le_rfl (pow_le_pow_left' inc 3))) le_rfl

theorem wideCoordinateBound_floor (hw : S.vp.params.n ≠ 16) (L q qs : ℕ) :
    1 ≤ wideCoordinateBound S L q qs := by
  apply (class_two_floor S hw L q qs).trans
  unfold wideCoordinateBound wideCompressionLoss
  exact le_add_self.trans (le_self_add.trans (le_self_add.trans le_self_add))
end Reduction.Compression
#print axioms Reduction.Compression.class_two_floor
#print axioms Reduction.Compression.wideCoordinateBound_floor
