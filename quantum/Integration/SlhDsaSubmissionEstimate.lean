import Integration.SlhDsaForsCoverageFloor

/-! The coefficient in the generic work estimate in §7.1.1 of the
SPHINCS+ v3.1 submission. Independent digest coverage and a uniform
n-byte guess are the two terms. It is distinct from adaptive forgery. -/
namespace Reduction.ForsLifetime
open QItsr MLink PQ.QROM ENNReal
set_option exponentiation.threshold 2048

noncomputable def submissionCoefficient (S : Sha2Set) (s : ℕ) : ℝ≥0∞ :=
  ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ + coverProb (Fin s) (SetDigest.idxCov S.vp)

/-- The binomial occupancy expression in the submission sums over the
number of signatures selecting the same FORS instance as a fresh digest. -/
theorem submission_binomial (S : Sha2Set) (s : ℕ) :
    submissionCoefficient S s = ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ +
      ∑ i ∈ Finset.range (s+1), (s.choose i : ℝ≥0∞) * ((2:ℝ≥0∞)^S.vp.params.h)⁻¹^i *
        (1-((2:ℝ≥0∞)^S.vp.params.h)⁻¹)^(s-i) *
        (1-(1-((2:ℝ≥0∞)^S.vp.params.a)⁻¹)^i)^S.vp.params.k := by
  rw [submissionCoefficient, digest_coverage_exact, coverProb_fors]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

/-- The coefficient in units of 2^(-8n), scaled by 32 so every
row has an integer certificate. -/
def scaledCeiling : Sha2Set → ℕ
  | .s128s => 33 | .s128f => 64 | .s192s => 48 | .s192f => 40
  | .s256s | .s256f => 96

theorem submission_interval (S : Sha2Set) (s : ℕ) (life : s ≤ 2^64) :
    ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ ≤ submissionCoefficient S s ∧
    submissionCoefficient S s ≤ (scaledCeiling S : ℝ≥0∞) / 32 * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  unfold submissionCoefficient
  refine ⟨le_self_add, (add_le_add le_rfl (lifetime_cover S s life)).trans ?_⟩
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  have width : 8*S.vp.params.n = (match S with
      | .s128s | .s128f => 128 | .s192s | .s192f => 192 | .s256s | .s256f => 256) := by
    cases S <;> decide
  rw [width]
  cases S <;> norm_num [scaledCeiling,coverageBits]

/-- The 256f coefficient exceeds twice the uniform node-guess term. -/
theorem submission_256f_floor :
    ((2:ℝ≥0∞)^255)⁻¹ < submissionCoefficient .s256f (2^64) := by
  have eq : ((2:ℝ≥0∞)^255)⁻¹ = ((2:ℝ≥0∞)^256)⁻¹ + ((2:ℝ≥0∞)^256)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) [ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_pow]
    norm_num
  rw [eq]
  exact ENNReal.add_lt_add_left (by finiteness) encoded_256f_floor

end Reduction.ForsLifetime
#print axioms Reduction.ForsLifetime.submission_interval
#print axioms Reduction.ForsLifetime.submission_256f_floor
#print axioms Reduction.ForsLifetime.submission_binomial
