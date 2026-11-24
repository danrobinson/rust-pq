import Integration.SlhDsaCompressionSmallClosed
import MReduction.Resources
namespace Reduction.Compression
open MLink Ideal SLHDSA ENNReal
variable (S : Sha2Set)

/-- The full honest target walk already exceeds the birthday threshold for a
128-bit prefix on both small parameter sets. -/
theorem small_walk_birthday_floor (hn : S.vp.params.n = 16) :
    2^128 ≤ (tcrTargets S.vp * ClassCollision.walkMax S)^2 := by
  cases S <;> first | exact (by contradiction) |
    (rw [MReduction.tcrTargets_128s_val]; decide +kernel) |
    (rw [MReduction.tcrTargets_128f_val]; decide +kernel)

set_option maxRecDepth 8192 in
/-- Counting the complete honest walk as quantum queries makes the previous
prefix-collision estimate vacuous at every arity and even at zero forger queries. -/
theorem small_class_floor (hn : S.vp.params.n = 16) (L q qs ar : ℕ) :
    1 ≤ 16*((SmallClass.budget S L q qs ar : ℝ≥0∞)+1)^3 / 2^128 := by
  let t := tcrTargets S.vp * ClassCollision.walkMax S
  have ht : 2^128 ≤ t^2 := small_walk_birthday_floor S hn
  have n : 2^128 ≤ 16*t^3 := by
    have pos : 1 ≤ t := by
      by_contra! h
      have hz : t = 0 := by omega
      simp [hz] at ht
    nlinarith only [ht,Nat.mul_le_mul_left (t^2) pos]
  have le : t ≤ SmallClass.budget S L q qs ar := by unfold t SmallClass.budget; omega
  have h : (t:ℝ≥0∞) ≤ (SmallClass.budget S L q qs ar : ℝ≥0∞)+1 :=
    (Nat.cast_le.mpr le).trans le_self_add
  have a : (2:ℝ≥0∞)^128 ≤ 16*(t:ℝ≥0∞)^3 := by exact_mod_cast n
  let D : ℝ≥0∞ := 2^128
  have h₁ : D ≠ 0 := by dsimp [D]; positivity
  have h₂ : D ≠ ⊤ := by dsimp [D]; finiteness
  change 1 ≤ _ / D
  rw [div_eq_mul_inv]
  exact (ENNReal.mul_inv_cancel h₁ h₂).ge.trans (mul_le_mul' (a.trans
    (mul_le_mul' le_rfl (pow_le_pow_left' h 3))) le_rfl)

theorem smallBound_floor (hn : S.vp.params.n = 16) (L q qs : ℕ) :
    1 ≤ smallBound S L q qs := by
  apply (small_class_floor S hn L q qs 2).trans
  unfold smallBound
  exact (le_add_self.trans (le_self_add.trans (le_self_add.trans (le_self_add.trans
    (le_self_add.trans (le_self_add.trans le_self_add)))))).trans le_add_self

end Reduction.Compression
#print axioms Reduction.Compression.small_walk_birthday_floor
#print axioms Reduction.Compression.small_class_floor
#print axioms Reduction.Compression.smallBound_floor
