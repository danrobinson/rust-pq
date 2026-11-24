import Integration.SlhDsaSetClosed

namespace Reduction.SetOracle
open MLink ENNReal

/-- Numerator of all terms except ITSR when written over the common node-space size. -/
def otherNumerator (S : Sha2Set) (q qs : ℕ) : ℕ :=
  let r := componentCounts S.vp qs
  let search := fun n => (2 * (q + n) + 1)^2
  16*q^2 + 168*(q+r.dspr)^2 + 3*search r.tcrFv +
    (search r.tcr1 + search r.tcr2 + search r.tcrLen + search r.tcrK) +
    (S.vp.params.w-2)*8*(q+r.ud)^2 + 2*search r.pre + search r.tcrT

private theorem eps_scaled (k q n : ℕ) :
    ENNReal.ofReal ((k : ℝ)*q^2 / 2^n) = (k : ℝ≥0∞)*q^2 / 2^n := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity)]
  simp

theorem componentForgeryBound_split (S : Sha2Set) (q qs : ℕ) :
    componentForgeryBound S q qs = itsrBound S.vp.params (q + (componentCounts S.vp qs).itsr) qs +
      (otherNumerator S q qs : ℝ≥0∞) / 2^(8*S.vp.params.n) := by
  have hud (x : ℕ) : epsUdSet S x = 8*(x:ℝ≥0∞)^2 / 2^(8*S.vp.params.n) :=
    eps_scaled 8 x _
  have hd (x : ℕ) : epsDsprSet S x = 168*(x:ℝ≥0∞)^2 / 2^(8*S.vp.params.n) :=
    eps_scaled 168 x _
  unfold componentForgeryBound epsTcrSet epsPreSet otherNumerator
  simp only [hud, hd,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- Benchmark exponents at 2^40 quantum port queries and 2^20 signatures. -/
def benchmarkBits : Sha2Set → ℕ
  | .s128s => 22
  | .s128f => 21
  | .s192s => 81
  | .s192f => 85
  | .s256s => 147
  | .s256f => 149

theorem componentForgeryBound_num (S : Sha2Set) :
    componentForgeryBound S (2^40) (2^20) ≤ ((2:ℝ≥0∞)^(benchmarkBits S))⁻¹ := by
  by_cases h : S = .s128s
  · subst S; exact componentCounts_128s_num
  let n := 8*S.vp.params.n
  let b := benchmarkBits S
  have hbits : b+1 ≤ n - 2*itsrQueryBits S - 22 := by cases S <;> first | contradiction | decide +kernel
  have hnum : otherNumerator S (2^40) (2^20) ≤ 2^(n-(b+1)) := by cases S <;> first | contradiction | decide +kernel
  have hnb : b+1 ≤ n := by omega
  rw [componentForgeryBound_split, div_eq_mul_inv]
  have he : (otherNumerator S (2^40) (2^20) : ℝ≥0∞) ≤ 2^(n-(b+1)) := by exact_mod_cast hnum
  calc _ ≤ ((2:ℝ≥0∞)^(b+1))⁻¹ + 2^(n-(b+1)) * ((2:ℝ≥0∞)^n)⁻¹ :=
          add_le_add ((itsrBound_sets_num S).trans (Num.inv_two_pow_le _ _ hbits)) (mul_le_mul' he le_rfl)
       _ = _ := by
         rw [Num.two_pow_mul_inv _ _ (by omega), show n-(n-(b+1)) = b+1 by omega, ← two_mul]
         simpa [b] using Num.two_pow_mul_inv 1 (b+1) (by omega)
end Reduction.SetOracle

#print axioms Reduction.SetOracle.componentForgeryBound_num
