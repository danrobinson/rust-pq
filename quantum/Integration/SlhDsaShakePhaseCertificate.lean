import Integration.SlhDsaShakeLifetimeCertificate

namespace Reduction.ShakeAdaptive
open MLink ENNReal PQ.QROM
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- Cost expression for a split phase-table simulation. This is an arithmetic
certificate; using it for a particular adversary requires proving the
correspondence to the two phase-table experiments. -/
noncomputable def phaseDigestLoss (S : Sha2Set) (q s : ℕ) : ℝ≥0∞ :=
  let Q := q+itsrHashes S.vp s
  let size := (2:ℝ≥0∞)^(8*S.vp.params.n)
  let p := coverProb (Fin s) (QItsr.SetDigest.idxCov S.vp)
  (((2*(Q:ℝ≥0∞)+1)^2*p)^(2⁻¹:ℝ) + 2*q*((s:ℝ≥0∞)*size⁻¹)^(2⁻¹:ℝ))^2 +
    ((s.choose 2+s:ℕ):ℝ≥0∞) / size

def phaseBits : Sha2Set → ℕ
  | .s128s | .s128f => 0
  | .s192s => 13 | .s192f => 21 | .s256s => 77 | .s256f => 83

theorem phase_lifetime_certificate (S : Sha2Set) (wide : 24 ≤ S.vp.params.n) :
    ShakeXof.repeatedLoss S (2^40) (2^64) (phaseDigestLoss S (2^40) (2^64)) ≤
      ((2:ℝ≥0∞)^(phaseBits S))⁻¹ := by
  let q : ℕ := 2^40
  let s : ℕ := 2^64
  let Q := q+itsrHashes S.vp s
  let loss := ((2*(2*Q+1)+2*q*2^32)^2 + (s.choose 2+s)) + ShakeXof.hashNumerator S q s
  have arithmetic : loss * 2^(phaseBits S) ≤ 2^(8*S.vp.params.n) := by
    simp only [loss,Nat.choose_two_right]
    cases S <;> revert wide <;> decide +kernel
  have digest := ForsLifetime.search_programming_numerator S Q q s 32 _
    (ForsLifetime.lifetime_cover S s le_rfl) le_rfl
  rw [ShakeXof.repeatedLoss_split]
  unfold phaseDigestLoss
  apply (add_le_add (add_le_add digest le_rfl) le_rfl).trans
  rw [← ENNReal.add_div,← Nat.cast_add,← ENNReal.add_div,← Nat.cast_add]
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    ForsLifetime.fraction_certificate loss (2^(phaseBits S)) _ arithmetic
end Reduction.ShakeAdaptive
#print axioms Reduction.ShakeAdaptive.phase_lifetime_certificate
