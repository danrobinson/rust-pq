import Integration.SlhDsaLifetimeNumerator
import Integration.SlhDsaShakeXofRepeated

namespace Reduction.ShakeXof
open MLink ENNReal
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- Integer numerator for the non-digest terms in the shared XOF reduction. -/
def hashNumerator (S : Sha2Set) (q s : ℕ) : ℕ :=
  let f := q+forsMHashes S.vp s
  let a := q+tcrMHashes S.vp s
  let search := fun x : ℕ => (2*x+1)^2
  8*(ShakeApi.Sk.budget S q s)^2 + 8*(ShakeApi.Msg.budget S q s)^2 +
    (168*f^2+3*search f) + 4*search a +
    (S.vp.params.w-2)*8*(q+qmWotsUdHashes S.vp s)^2 +
    2*search (q+qmWotsPreHashes S.vp s) + search (q+qmWotsTcrTHashes S.vp s)

theorem repeatedLoss_split (S : Sha2Set) (q s : ℕ) (risk : ℝ≥0∞) :
    repeatedLoss S q s risk = risk + (hashNumerator S q s : ℝ≥0∞)/2^(8*S.vp.params.n) := by
  have scaled (k t : ℕ) : ENNReal.ofReal ((k:ℝ)*t^2 / 2^(8*S.vp.params.n)) =
      (k:ℝ≥0∞)*t^2 / 2^(8*S.vp.params.n) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity)]
    simp
  unfold repeatedLoss hashNumerator epsTcr SetOracle.epsPreSet SetOracle.epsUdSet
  simp only [← Nat.cast_ofNat (R := ℝ) (n := 8), ← Nat.cast_ofNat (R := ℝ) (n := 168), scaled]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,div_eq_mul_inv]
  ring

def adaptiveNumerator (S : Sha2Set) (q s l : ℕ) : ℕ :=
  let t := q+itsrHashes S.vp s
  (2*(2*t+1)+2*t*2^l)^2 + hashNumerator S q s

/-- Numerical end of the reduction when its digest game is charged at the
full number of public and honest hash queries. -/
theorem adaptive_loss_certificate (S : Sha2Set) (q s l divisor : ℕ)
    (life : s ≤ 2^64) (signings : s ≤ 2^(2*l))
    (cert : adaptiveNumerator S q s l * divisor ≤ 2^(8*S.vp.params.n)) :
    repeatedLoss S q s (itsrBound S.vp.params (q+itsrHashes S.vp s) s) ≤ (divisor:ℝ≥0∞)⁻¹ := by
  rw [repeatedLoss_split]
  apply (add_le_add (ForsLifetime.digest_numerator S _ s l life signings) le_rfl).trans
  rw [← ENNReal.add_div,← Nat.cast_add]
  exact ForsLifetime.fraction_certificate _ _ _ cert
/-- Even with no public queries, the randomizer-programming term alone
exceeds the probability budget for the four narrower sets at a full lifetime.
This lower bound concerns the analytic estimate. -/
theorem narrower_lifetime_programming_floor (S : Sha2Set) (width : S.vp.params.n ≤ 24) :
    1 ≤ itsrBound S.vp.params (itsrHashes S.vp (2^64)) (2^64) := by
  let q := itsrHashes S.vp (2^64)
  let m := 4*S.vp.params.n-32
  have bits : 8*S.vp.params.n-64 = m*2 := by cases S <;> decide
  have hn : 64 ≤ 8*S.vp.params.n := by cases S <;> decide
  have work : 2^m ≤ 2*q := by cases S <;> revert width <;> decide +kernel
  have hc : (2:ℝ≥0∞)^m ≤ 2*q := by exact_mod_cast work
  have hs : (2:ℝ≥0∞)^64 * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ = (((2:ℝ≥0∞)^m)⁻¹)^2 := by
    rw [Num.two_pow_mul_inv _ _ hn,Num.inv_two_pow_pow,bits]
  unfold itsrBound
  simp only [Nat.cast_pow,Nat.cast_ofNat,hs,Num.sq_rpow_half]
  apply le_trans _ (pow_le_pow_left₀ zero_le (le_add_self : 2*(q:ℝ≥0∞)*((2:ℝ≥0∞)^m)⁻¹ ≤ _ + _) 2)
  have atLeast : 1 ≤ 2*(q:ℝ≥0∞)*((2:ℝ≥0∞)^m)⁻¹ := by
    apply le_trans _ (mul_le_mul' hc le_rfl)
    rw [Num.two_pow_mul_inv m m le_rfl,Nat.sub_self,pow_zero,inv_one]
  simpa using pow_le_pow_left₀ zero_le atLeast 2

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.adaptive_loss_certificate
#print axioms Reduction.ShakeXof.narrower_lifetime_programming_floor
