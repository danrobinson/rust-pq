import Integration.SlhDsaSetItsr
import Mathlib.Combinatorics.Enumerative.Stirling

namespace Reduction.ForsLifetime
open QItsr MLink SLHDSA PQ.QROM ENNReal Finset
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

private noncomputable def mass (s i : ℕ) (p : ℝ≥0∞) :=
  (s.choose i : ℝ≥0∞) * p^i * (1-p)^(s-i)

private theorem factorial_moment (s j : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) :
    ∑ i ∈ range (s+1), mass s i p * (i.descFactorial j : ℝ≥0∞) = (s.descFactorial j : ℝ≥0∞)*p^j := by
  by_cases hj : j ≤ s
  case neg =>
    rw [Nat.descFactorial_of_lt (by omega : s < j),Nat.cast_zero,zero_mul]
    exact sum_eq_zero fun i hi => by
      rw [Nat.descFactorial_of_lt (by have := mem_range.mp hi; omega : i < j),Nat.cast_zero,mul_zero]
  have shift : ∑ i ∈ range j, mass s i p * (i.descFactorial j : ℝ≥0∞) = 0 :=
    sum_eq_zero fun i hi => by rw [Nat.descFactorial_of_lt (mem_range.mp hi)]; simp
  have coeff (i : ℕ) : s.choose (j+i) * (j+i).descFactorial j = s.descFactorial j * (s-j).choose i := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose]
    rw [mul_left_comm, Nat.choose_mul (Nat.le_add_right j i), Nat.add_sub_cancel_left]
    ac_rfl
  rw [show s+1 = j+(s-j+1) by omega, sum_range_add,shift,zero_add]
  calc
    _ = ∑ i ∈ range (s-j+1), (s.descFactorial j : ℝ≥0∞)*p^j *
        (p^i * (1-p)^(s-j-i) * ((s-j).choose i : ℝ≥0∞)) := by
      apply sum_congr rfl; intro i _
      have cc : (s.choose (j+i) : ℝ≥0∞)*((j+i).descFactorial j : ℝ≥0∞) =
          (s.descFactorial j : ℝ≥0∞)*((s-j).choose i : ℝ≥0∞) := by exact_mod_cast coeff i
      unfold mass
      rw [pow_add, Nat.sub_add_eq]
      calc
        _ = ((s.choose (j+i) : ℝ≥0∞)*((j+i).descFactorial j : ℝ≥0∞)) * (p^j*p^i*(1-p)^(s-j-i)) := by ac_rfl
        _ = _ := by rw [cc]; ac_rfl
    _ = _ := by rw [← mul_sum,← add_pow,add_tsub_cancel_of_le hp,one_pow,mul_one]

/-- The chance a fresh independent digest is covered by s independent digests.
The sum has k+1 terms even when s is the full lifetime signing budget. -/
theorem cover_moment (s k : ℕ) (p t : ℝ≥0∞) (hp : p ≤ 1) (ht : t ≤ 1) :
    ∑ i ∈ range (s+1), ((s.choose i : ℝ≥0∞)*p^i*(1-p)^(s-i))*(1-(1-t)^i)^k ≤
      (∑ j ∈ range (k+1), (Nat.stirlingSecond k j : ℝ≥0∞)*((s:ℝ≥0∞)*p)^j)*t^k := by
  have powers (i : ℕ) : (i:ℝ≥0∞)^k = ∑ j ∈ range (k+1), (Nat.stirlingSecond k j : ℝ≥0∞)*(i.descFactorial j : ℝ≥0∞) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i k
  calc
    _ ≤ ∑ i ∈ range (s+1), (mass s i p * (i:ℝ≥0∞)^k)*t^k := by
      apply sum_le_sum; intro i _
      rw [mul_assoc (mass s i p),← mul_pow]
      exact mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le (Num.one_sub_one_sub_pow_le _ ht i) _)
    _ = (∑ i ∈ range (s+1), ∑ j ∈ range (k+1),
      (Nat.stirlingSecond k j : ℝ≥0∞)*(mass s i p*(i.descFactorial j : ℝ≥0∞)))*t^k := by
      rw [← sum_mul]
      apply congrArg (·*t^k)
      apply sum_congr rfl; intro i _
      rw [powers,mul_sum]
      apply sum_congr rfl; intro j _; ac_rfl
    _ ≤ _ := by
      rw [sum_comm]
      apply mul_le_mul' _ le_rfl
      apply sum_le_sum; intro j hj
      rw [← mul_sum, factorial_moment s j p hp,mul_pow]
      gcongr
      exact_mod_cast Nat.descFactorial_le_pow s j

/-- Clearing the common denominators leaves a short natural-number certificate. -/
theorem moment_certificate (s k h a b : ℕ)
    (cert : (∑ j ∈ range (k+1), Nat.stirlingSecond k j * s^j * (2^h)^(k-j)) * 2^b ≤
      (2^h)^k * (2^a)^k) :
    (∑ j ∈ range (k+1), (Nat.stirlingSecond k j : ℝ≥0∞)*((s:ℝ≥0∞)*((2:ℝ≥0∞)^h)⁻¹)^j)*
      (((2:ℝ≥0∞)^a)⁻¹)^k ≤ ((2:ℝ≥0∞)^b)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.sum_ne_top.mpr (fun i _ => by finiteness)) (by finiteness)) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_sum,ENNReal.toReal_inv,ENNReal.toReal_pow,
    ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  have eq : (∑ j ∈ range (k+1), (Nat.stirlingSecond k j : ℝ)*((s:ℝ)*((2:ℝ)^h)⁻¹)^j) *
      ((2:ℝ)^h)^k = (∑ j ∈ range (k+1), Nat.stirlingSecond k j * s^j * (2^h)^(k-j) : ℕ) := by
    rw [sum_mul,Nat.cast_sum]
    apply sum_congr rfl; intro j hj
    have hi : j+(k-j)=k := by have := mem_range.mp hj; omega
    nth_rw 2 [← hi]
    simp only [pow_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow,inv_pow]
    field_simp
  have co : ((∑ j ∈ range (k+1), Nat.stirlingSecond k j * s^j * (2^h)^(k-j) : ℕ):ℝ)*2^b ≤
      ((2:ℝ)^h)^k*((2:ℝ)^a)^k := by exact_mod_cast cert
  rw [← eq] at co
  simp only [inv_pow]
  field_simp
  simp only [← div_eq_mul_inv] at co
  apply le_of_mul_le_mul_left (a := ((2:ℝ)^h)^k) _ (by positivity)
  linarith only [co]

def coverageBits : Sha2Set → ℕ
  | .s128s => 133 | .s128f => 128 | .s192s => 193
  | .s192f => 194 | .s256s => 255 | .s256f => 255

private theorem lifetime_sum (S : Sha2Set) (s : ℕ) (limit : s ≤ 2^64) :
    (∑ i ∈ range (s+1), (s.choose i : ℝ≥0∞) * ((2:ℝ≥0∞)^S.vp.params.h)⁻¹^i *
      (1-((2:ℝ≥0∞)^S.vp.params.h)⁻¹)^(s-i) * (1-(1-((2:ℝ≥0∞)^S.vp.params.a)⁻¹)^i)^S.vp.params.k) ≤
    ((2:ℝ≥0∞)^(coverageBits S))⁻¹ := by
  apply (cover_moment _ _ _ _ (by simp; exact one_le_pow₀ (by norm_num)) (by simp; exact one_le_pow₀ (by norm_num))).trans
  have certificate : (∑ j ∈ range (S.vp.params.k+1), Nat.stirlingSecond S.vp.params.k j *
      (2^64)^j * (2^S.vp.params.h)^(S.vp.params.k-j)) * 2^(coverageBits S) ≤
      (2^S.vp.params.h)^S.vp.params.k * (2^S.vp.params.a)^S.vp.params.k := by cases S <;> decide +kernel
  apply moment_certificate
  apply le_trans _ certificate
  gcongr

theorem lifetime_cover (S : Sha2Set) (s : ℕ) (limit : s ≤ 2^64) :
    coverProb (Fin s) (SetDigest.idxCov S.vp) ≤ ((2:ℝ≥0∞)^(coverageBits S))⁻¹ := by
  have prob := SetDigest.coverProb_idxCov_le S.vp s
  rw [coverProb_fors] at prob
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at prob
  apply prob.trans
  exact lifetime_sum S s limit

/-- In the adaptive digest-game estimate the randomizer-programming loss
survives even after accounting tightly for the independent target digests. -/
theorem adaptive_digest_loss (S : Sha2Set) (q s : ℕ) (limit : s ≤ 2^64) :
    itsrBound S.vp.params q s ≤
      (((2*(q:ℝ≥0∞)+1)^2*((2:ℝ≥0∞)^(coverageBits S))⁻¹)^(2⁻¹:ℝ) +
        2*q*((s:ℝ≥0∞)*((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹)^(2⁻¹:ℝ))^2 := by
  unfold itsrBound
  gcongr
  exact lifetime_sum S s limit

end Reduction.ForsLifetime
#print axioms Reduction.ForsLifetime.cover_moment
#print axioms Reduction.ForsLifetime.lifetime_cover
#print axioms Reduction.ForsLifetime.adaptive_digest_loss
