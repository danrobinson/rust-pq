import Integration.SlhDsaShakePermutationMsgPostGame
import Integration.SlhDsaBridgePrf

namespace Reduction.ShakePermutation.MsgTrajectory
open Classical MLink SLHDSA SetOracle ENNReal OracleComp Quantum PQ.Interactive
open scoped Kronecker ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
attribute [local instance] singletonFintype
variable (S : Sha2Set) (π : Permutation) (bs : List Rate) (r : S.Node) (x : S.Node → Words)
variable {E : Type} [Fintype E] [DecidableEq E]

private theorem avg_mul {A : Type} [Fintype A] (c : ℝ≥0∞) (f : A → ℝ≥0∞) :
    uniformMean (fun a => c*f a) = c*uniformMean f := by
  simp only [uniformMean,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..

private theorem normalized {T : Type} [Fintype T] [DecidableEq T]
    (A : Matrix (T × Unit) (T × Unit) ℂ) (pos : A.PosSemidef) (nonzero : A.trace.re ≠ 0) :
    ∃ ρ : SubState T, (A.trace.re:ℂ) • (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) = A := by
  let t := A.trace.re
  have tr : (t:ℂ) = A.trace := Complex.ext rfl (Complex.nonneg_iff.mp pos.trace_nonneg).2
  have positive : 0 < t := lt_of_le_of_ne pos.trace_re_nonneg (Ne.symm nonzero)
  let B := ((t⁻¹:ℝ):ℂ) • A
  have pb : B.PosSemidef := pos.smul (Complex.nonneg_iff.mpr ⟨inv_nonneg.mpr positive.le,rfl⟩)
  have tb : B.trace = 1 := by unfold B; rw [Matrix.trace_smul,← tr]; simp [smul_eq_mul,show t ≠ 0 from nonzero]
  obtain ⟨ρ,hρ⟩ := exists_subState B pb tb
  refine ⟨ρ,?_⟩
  rw [← hρ]; simp [B,smul_smul,show t ≠ 0 from nonzero,t]
private theorem number : ENNReal.ofReal (8*((2^41:ℕ):ℝ)^2*((2:ℝ)^126)⁻¹) = ((2:ℝ≥0∞)^41)⁻¹ := by
  rw [← ENNReal.ofReal_ofNat (n:=2),← ENNReal.ofReal_pow (by norm_num),← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  norm_num
set_option allowUnsafeReducibility true in
attribute [local irreducible] programmed oracle

/-- At the benchmark, a measured branch pays its trace weight times the
postchallenge error. This allows all classical branch outputs to be summed. -/
theorem post_mass (M : (Port → Words) → Closed (WS Port Words E) Bool)
    (hq : PUE (spec:=unifSpec) cnt0 M (2^41)) (A : Matrix (WS Port Words E) (WS Port Words E) ℂ)
    (pos : A.PosSemidef) :
    let test := fun δ => qWeight (· = true) (M (oracle δ)) A
    posterior S π bs r x (fun k σ => test (programmed S k π σ)) ≤ test π +
      ENNReal.ofReal A.trace.re * ((2:ℝ≥0∞)^41)⁻¹ := by
  dsimp only
  let t := A.trace.re
  by_cases zero : t = 0
  · have w0 (H) : qWeight (· = true) (M H) A = 0 := le_antisymm ((qWeight_le_trace _ _ pos).trans_eq (by
      change ENNReal.ofReal t = 0; rw [zero,ENNReal.ofReal_zero])) zero_le
    simp only [w0,posterior,uniformMean,mul_zero,Finset.sum_const_zero,zero_le]
  · obtain ⟨ρ,scale⟩ := normalized _ pos zero
    have wt (H) : qWeight (· = true) (M H) A = ENNReal.ofReal t *
        qWeight (· = true) (M H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
      exact (congrArg (qWeight (· = true) (M H)) scale.symm).trans
        (qWeight_smul _ _ t pos.trace_re_nonneg _)
    have h := post_game S π bs r x M (2^41) hq ρ
    rw [number] at h
    simp only [wt,posterior,avg_mul]
    exact (mul_le_mul' (le_refl (ENNReal.ofReal t)) h).trans_eq (mul_add ..)

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.post_mass
