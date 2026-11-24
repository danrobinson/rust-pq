import Integration.SlhDsaShakePermutationMsgRounds
import Integration.SlhDsaShakePermutationOverlapGame

namespace Reduction.ShakePermutation.MsgEffect
open Classical Quantum OracleComp OracleSpec PQ.Interactive ENNReal Matrix
open scoped ComplexOrder
noncomputable section
variable {W A : Type} [Fintype W]
def mass (p : Closed W Bool) (M : Matrix W W ℂ) := (qWeight (· = true) p M).toReal

theorem finite_weight (p : Closed W Bool) {M : Matrix W W ℂ} (h : M.PosSemidef) :
    qWeight (· = true) p M ≠ ⊤ := ne_top_of_le_ne_top ofReal_ne_top (qWeight_le_trace _ _ h)

theorem mass_le (p : Closed W Bool) {M : Matrix W W ℂ} (h : M.PosSemidef) :
    mass p M ≤ M.trace.re := by
  simpa only [mass,toReal_ofReal h.trace_re_nonneg] using
    ENNReal.toReal_mono ofReal_ne_top (qWeight_le_trace (· = true) p h)

theorem mass_instr (j : InstrIdx W) (k : Fin (j.1 + 1) → Closed W Bool) {M : Matrix W W ℂ}
    (h : M.PosSemidef) :
    mass (liftM ((instrSpec W + unifSpec).query (.inl j)) >>= k) M =
      ∑ i, mass (k i) (j.2.1.branch i M) := by
  rw [mass,qWeight_instr_bind,ENNReal.toReal_sum (fun i _ => finite_weight _ ((j.2.1.isCP_branch i).posSemidef h))]
  rfl

theorem mass_coin (n : ℕ) (k : Fin (n+1) → Closed W Bool) {M : Matrix W W ℂ} (h : M.PosSemidef) :
    mass (liftM ((instrSpec W + unifSpec).query (.inr n)) >>= k) M =
      ((n:ℝ)+1)⁻¹ * ∑ i, mass (k i) M := by
  rw [mass,qWeight_unif_bind,ENNReal.toReal_mul,ENNReal.toReal_sum (fun i _ => finite_weight _ h)]
  simp [mass,ENNReal.toReal_add]

/-- The chosen future computation can depend on hidden data. Its effect
on the current quantum state remains a positive linear test. -/
theorem linear_test (p : Closed W Bool) :
    ∃ L : Matrix W W ℂ →ₗ[ℂ] ℂ, ∀ M : Matrix W W ℂ, M.PosSemidef → (L M).re = mass p M := by
  induction p using OracleComp.inductionOn with
  | pure b =>
    cases b
    · exact ⟨0,fun _ _ => by simp [mass]⟩
    · exact ⟨traceLinearMap W ℂ ℂ,fun M h => by simp [mass,h.trace_re_nonneg]⟩
  | query_bind t k ih =>
    choose L hL using ih
    rcases t with j|n
    · refine ⟨∑ i, (L i).comp (j.2.1.branch i),fun M h => ?_⟩
      rw [mass_instr _ _ h,LinearMap.sum_apply,Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => hL i _ ((j.2.1.isCP_branch i).posSemidef h)
    · refine ⟨((((n:ℝ)+1)⁻¹:ℝ):ℂ) • ∑ i, L i,fun M h => ?_⟩
      rw [mass_coin _ _ h,LinearMap.smul_apply,smul_eq_mul,Complex.re_ofReal_mul,LinearMap.sum_apply,Complex.re_sum]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => hL i _ h)

/-- Young's inequality for any measured continuation, expressed directly
as an operator identity with one positive rank-one remainder. -/
theorem shift (p : Closed W Bool) (v d : EuclideanSpace ℂ W) (a : ℝ) (ha : 0 < a) :
    mass p (ketBra (v+d) (v+d)) ≤ mass p (ketBra v v) + a*‖v‖^2 + (1+1/a)*‖d‖^2 := by
  let K (z : EuclideanSpace ℂ W) := ketBra z z
  obtain ⟨L,hL⟩ := linear_test p
  have amt (z : EuclideanSpace ℂ W) := hL (K z) (posSemidef_ketBra_self z)
  have op : (a:ℂ) • K (v+d) + K ((a:ℂ) • v - d) = ((a:ℂ)+(a:ℂ)^2) • K v + ((a:ℂ)+1) • K d := by
    ext i j
    simp [K,ketBra_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have lin := congrArg (fun M => (L M).re) op
  simp only [map_add,map_smul,smul_eq_mul,Complex.add_re,Complex.re_ofReal_mul] at lin
  have clean : (((a:ℂ)+(a:ℂ)^2) * L (K v)).re = (a+a^2)*(L (K v)).re := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_add,Complex.re_ofReal_mul]
  have clean' : (((a:ℂ)+1) * L (K d)).re = (a+1)*(L (K d)).re := by
    rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.re_ofReal_mul]
  rw [clean,clean',amt,amt,amt,amt] at lin
  have hv : mass p (K v) ≤ ‖v‖^2 := (mass_le _ (posSemidef_ketBra_self v)).trans_eq (trace_re_ketBra_self v)
  have hd : mass p (K d) ≤ ‖d‖^2 := (mass_le _ (posSemidef_ketBra_self d)).trans_eq (trace_re_ketBra_self d)
  have nz : 0 ≤ mass p (K ((a:ℂ) • v - d)) := ENNReal.toReal_nonneg
  change mass p (K (v+d)) ≤ mass p (K v) + _ + _
  apply (mul_le_mul_iff_of_pos_left ha).mp
  have e : a*(1+1/a) = a+1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg a), mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ a+1),
    congrArg (fun t => t*‖d‖^2) e]

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.shift
