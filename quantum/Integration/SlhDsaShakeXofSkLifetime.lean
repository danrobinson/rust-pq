import Integration.SlhDsaShakeXofSkOpenCost
import Integration.SlhDsaShakeXofMixedColumn

namespace Reduction.ShakeApi.Sk.Mixed
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker ComplexOrder
set_option exponentiation.threshold 2048

theorem real_le_ideal (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
    (cap : 2*S.vp.params.n+32 ≤ N) (q s : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) :
    let A := fun H : RawTable S N => qbPrfWC sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (skPrfC S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) + ShakeXof.mixedPrfLoss S q (Sk.budget S 0 s) := by
  intro A
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input N × Bytes S.vp.params.m) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  have unit : ρ.matrix.trace = 1 := by simpa [hρ,Matrix.trace_kronecker] using F.trace_eq_one
  rw [hρ]
  exact ShakeXof.mixed_sk_prf S cap A (machine S N rand seeds F) q (Sk.budget S 0 s)
    (represented S N rand seeds F) (fun a => public_cost S N rand seeds F a q hq)
    (fun a => read_cost S N rand seeds F a s hs) ρ unit


/-- Dyadic exponents for a single keyed SHAKE game at 2^40 coherent
queries and its full honest key-lifetime read budget. -/
def lifetimePrfBits : Sha2Set → ℕ
  | .s128s => 41 | .s128f => 43 | .s192s => 105
  | .s192f => 107 | .s256s => 169 | .s256f => 171

theorem lifetime_prf_loss (S : Sha2Set) (t : ℕ)
    (ht : t ≤ max (Sk.budget S 0 (2^64)) (Msg.budget S 0 (2^64))) :
    ShakeXof.mixedPrfLoss S (2^40) t ≤ ((2:ℝ≥0∞)^lifetimePrfBits S)⁻¹ := by
  let T := max (Sk.budget S 0 (2^64)) (Msg.budget S 0 (2^64))
  let u := T.sqrt+1
  have bound : T ≤ u^2 := by cases S <;> decide +kernel
  have sq : (t:ℝ≥0∞) ≤ (u:ℝ≥0∞)^2 := by exact_mod_cast ht.trans bound
  have le := PQ.QROM.sqrt_le_sqrt sq
  rw [← ENNReal.rpow_natCast_mul] at le
  norm_num at le
  unfold ShakeXof.mixedPrfLoss
  simp only [← one_div (2:ℝ)]
  refine (add_le_add le_rfl (ENNReal.div_le_div_right (pow_le_pow_left' (add_le_add le le_rfl) 2) _)).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add,ENNReal.toReal_ofReal,
    ENNReal.toReal_pow,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,ENNReal.toReal_ofNat]
  field_simp
  norm_cast
  cases S <;> decide +kernel

/-- The real secret-address PRF term of the signature reduction stays
within the stated dyadic distance of its ideal counterpart over a key lifetime. -/
theorem signature_lifetime (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
    (cap : 2*S.vp.params.n+32 ≤ N) (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) (2^64)) :
    let A := fun H : RawTable S N => qbPrfWC sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (skPrfC S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) + ((2:ℝ≥0∞)^lifetimePrfBits S)⁻¹ :=
  (real_le_ideal S N rand seeds F cap _ _ hq hs).trans (add_le_add le_rfl (lifetime_prf_loss S _ (Nat.le_max_left ..)))

end Reduction.ShakeApi.Sk.Mixed
#print axioms Reduction.ShakeApi.Sk.Mixed.signature_lifetime
