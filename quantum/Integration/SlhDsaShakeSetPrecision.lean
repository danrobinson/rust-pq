import Integration.SlhDsaShakeXofSignature

namespace Reduction.ShakeXof
open OracleComp OracleSpec MLink SLHDSA SLHDSA.Security ENNReal Quantum PQ.Interactive
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- Raw queries charged to a signature reduction after expanding every
public permutation query and allowing for honest queries. -/
def expandedQueries : ℕ := ((8*483+4)*8+1)*2^40

private theorem parameters (S : Sha2Set) :
    (8*S.vp.params.n = 128 ∧ 231 ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k) ∨
    (8*S.vp.params.n = 192 ∧ 301 ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k) ∨
    (8*S.vp.params.n = 256 ∧ 372 ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k) := by
  cases S <;> decide +kernel

private theorem loss_le (S : Sha2Set) (q d : ℕ) (hd : d ≤ S.vp.params.h+S.vp.params.a*S.vp.params.k) :
    (singleLoss S q).toReal ≤
      (296*(q:ℝ)^2 + 10*(2*q+1)^2)/2^(8*S.vp.params.n) + 16*((q:ℝ)+1)^3/2^d := by
  have w : S.vp.params.w-2 = 14 := by cases S <;> decide
  unfold singleLoss SetOracle.epsUdSet SetOracle.epsPreSet
  rw [w]
  simp (disch := first | finiteness | positivity | norm_num) only [ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_ofReal]
  have h : 16*((q:ℝ)+1)^3/2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) ≤ 16*((q:ℝ)+1)^3/2^d := by
    gcongr; norm_num
  linarith only [h, show (296*(q:ℝ)^2 + 10*(2*q+1)^2)/2^(8*S.vp.params.n) =
    2*(8*(q:ℝ)^2/2^(8*S.vp.params.n)) + 168*(q:ℝ)^2/2^(8*S.vp.params.n) +
      8*((2*(q:ℝ)+1)^2/2^(8*S.vp.params.n)) + 14*(8*(q:ℝ)^2/2^(8*S.vp.params.n)) +
      (2*(q:ℝ)+1)^2*((2^(8*S.vp.params.n):ℝ)⁻¹+(2^(8*S.vp.params.n):ℝ)⁻¹) by ring]

private theorem finiteLoss (S : Sha2Set) (q : ℕ) : singleLoss S q ≠ ⊤ := by
  unfold singleLoss SetOracle.epsUdSet SetOracle.epsPreSet
  finiteness

theorem precision (S : Sha2Set) :
    singleLoss S (2^40+2^22) ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-89))⁻¹ ∧
    singleLoss S expandedQueries ≤ ((2:ℝ≥0∞)^(8*S.vp.params.n-119))⁻¹ := by
  rcases parameters S with ⟨bits,hd⟩ | ⟨bits,hd⟩ | ⟨bits,hd⟩ <;>
    constructor <;>
    apply (ENNReal.toReal_le_toReal (finiteLoss _ _) (by finiteness)).mp <;>
    apply (loss_le _ _ _ hd).trans <;>
    rw [bits] <;> norm_num [expandedQueries]

/-- Direct shared-XOF strong and existential forgery bounds at the public
benchmark, retaining the node width of the parameter set. -/
theorem signature_benchmark_precise (S : Sha2Set) (N : ℕ)
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
    (c : Caps) (msg : c.ml = 65536) (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤
      ((2:ℝ≥0∞)^(8*S.vp.params.n-89))⁻¹ ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤
      ((2:ℝ≥0∞)^(8*S.vp.params.n-89))⁻¹ := by
  obtain ⟨s,e⟩ := signature_queries (Q := 2^40+2^22) S N r seeds F (by decide) c msg cap hq hs hc
  exact ⟨s.trans (precision S).1,e.trans (precision S).1⟩

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.precision
#print axioms Reduction.ShakeXof.signature_benchmark_precise
