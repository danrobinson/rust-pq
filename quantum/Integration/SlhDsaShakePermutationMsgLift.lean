import Integration.SlhDsaShakePermutationMsgPrefixGame

namespace Reduction.ShakePermutation.MsgEffect
open Classical Quantum OracleComp OracleSpec PQ.Interactive ENNReal SetOracle QMsg
open scoped ComplexOrder
noncomputable section
variable {T U V W Z : Type} [Fintype T] [Fintype U] [Fintype W]

private theorem mean_sum {I : Type} [Fintype I] (f : T → I → ℝ≥0∞) :
    uniformMean (fun t => ∑ i, f t i) = ∑ i, uniformMean (fun t => f t i) := by
  simp only [uniformMean,Finset.mul_sum]
  exact Finset.sum_comm

private theorem mean_mul (c : ℝ≥0∞) (f : T → ℝ≥0∞) :
    uniformMean (fun t => c*f t) = c*uniformMean f := by
  simp only [uniformMean,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..

/-- Lift a comparison of two independently averaged ensembles through a
common quantum prefix. Only outputs satisfying the public challenge predicate
are charged. Both future tests can use the full surviving quantum state. -/
theorem under_prefix_event (p : Closed W Z) (valid ask : Z → Prop) [DecidablePred ask]
    (hp : AllQueries (fun _ => True) valid p) (l : T → Z → Closed W Bool)
    (r : U → Z → Closed W Bool) (ε : ℝ≥0∞)
    (step : ∀ z, valid z → ∀ M : Matrix W W ℂ, M.PosSemidef →
      uniformMean (fun t => qWeight (· = true) (l t z) M) ≤
        uniformMean (fun u => qWeight (· = true) (r u z) M) +
          ε*(if ask z then ENNReal.ofReal M.trace.re else 0))
    (M : Matrix W W ℂ) (pos : M.PosSemidef) :
    uniformMean (fun t => qWeight (· = true) (p >>= l t) M) ≤
      uniformMean (fun u => qWeight (· = true) (p >>= r u) M) + ε*qWeight ask p M := by
  induction p using OracleComp.inductionOn generalizing M with
  | pure z => simpa using step z hp M pos
  | query_bind t k ih =>
    simp only [bind_assoc]
    rcases t with j|n
    · simp only [qWeight_instr_bind,mean_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b _ => ih b (hp.2 b) _ ((j.2.1.isCP_branch b).posSemidef pos)
    · simp only [qWeight_unif_bind,mean_mul,mean_sum]
      let c := ((n:ℝ≥0∞)+1)⁻¹
      change c*∑ b, _ ≤ c*∑ b, _ + ε*(c*∑ b, _)
      rw [mul_left_comm ε c,← mul_add]
      apply mul_le_mul' le_rfl
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b _ => ih b (hp.2 b) M pos

theorem under_prefix (p : Closed W Z) (valid : Z → Prop)
    (hp : AllQueries (fun _ => True) valid p) (l : T → Z → Closed W Bool)
    (r : U → Z → Closed W Bool) (ε : ℝ≥0∞)
    (step : ∀ z, valid z → ∀ M : Matrix W W ℂ, M.PosSemidef →
      uniformMean (fun t => qWeight (· = true) (l t z) M) ≤
        uniformMean (fun u => qWeight (· = true) (r u z) M) + ε*ENNReal.ofReal M.trace.re)
    (M : Matrix W W ℂ) (pos : M.PosSemidef) :
    uniformMean (fun t => qWeight (· = true) (p >>= l t) M) ≤
      uniformMean (fun u => qWeight (· = true) (p >>= r u) M) + ε*ENNReal.ofReal M.trace.re := by
  simpa only [qWeight_true p pos] using under_prefix_event p valid (fun _ => True) hp l r ε step M pos

/-- Native game witnesses usually come as two successive uniform draws.
Both sides may factor in different finite sample spaces. -/
theorem under_two_draws {T' U' : Type} [Fintype T'] [Fintype U']
    (p : Closed W Z) (valid : Z → Prop) (hp : AllQueries (fun _ => True) valid p)
    (l : T → T' → Z → Closed W Bool) (r : U → U' → Z → Closed W Bool) (ε : ℝ≥0∞)
    (step : ∀ z, valid z → ∀ M : Matrix W W ℂ, M.PosSemidef →
      uniformMean (fun t => uniformMean (fun t' => qWeight (· = true) (l t t' z) M)) ≤
        uniformMean (fun u => uniformMean (fun u' => qWeight (· = true) (r u u' z) M)) +
          ε*ENNReal.ofReal M.trace.re)
    (M : Matrix W W ℂ) (pos : M.PosSemidef) :
    uniformMean (fun t => uniformMean (fun t' => qWeight (· = true) (p >>= l t t') M)) ≤
      uniformMean (fun u => uniformMean (fun u' => qWeight (· = true) (p >>= r u u') M)) +
        ε*ENNReal.ofReal M.trace.re := by
  have localStep (z) (hz : valid z) (M : Matrix W W ℂ) (h : M.PosSemidef) :
      uniformMean (fun t : T × T' => qWeight (· = true) (l t.1 t.2 z) M) ≤
      uniformMean (fun u : U × U' => qWeight (· = true) (r u.1 u.2 z) M) +
        ε*ENNReal.ofReal M.trace.re := by simpa only [Classic.mean_prod] using step z hz M h
  have all := under_prefix p valid hp (fun t : T × T' => l t.1 t.2)
    (fun u : U × U' => r u.1 u.2) ε localStep M pos
  simpa only [Classic.mean_prod] using all

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.under_two_draws
