import Integration.SlhDsaShakePermutationMsgLift

namespace Reduction.ShakePermutation.MsgEffect
open Classical MLink SLHDSA Quantum OracleComp OracleSpec PQ.Interactive SetOracle ENNReal MsgTrajectory
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.reassign

private def exchange {A J : Type} [Fintype A] [Fintype J] (c : J ↪ A)
    (p : Equiv.Perm A × Equiv.Perm A) : Equiv.Perm A × Equiv.Perm A :=
  let τ := Program.reassign (imageTuple c p.1) (imageTuple c p.2)
  (p.1.trans τ,p.2.trans τ.symm)

private theorem exchange_inv {A J : Type} [Fintype A] [Fintype J] (c : J ↪ A) :
    Function.Involutive (exchange c) := by
  rintro ⟨π,σ⟩
  let x := imageTuple c π
  let y := imageTuple c σ
  let τ := Program.reassign x y
  have forward : imageTuple c (π.trans τ) = y := by ext j; exact Program.reassign_hit x y j
  have inverse : imageTuple c (σ.trans τ.symm) = x := by
    ext j; exact (τ.symm_apply_eq).mpr (Program.reassign_hit x y j).symm
  change ((π.trans τ).trans (Program.reassign (imageTuple c (π.trans τ)) (imageTuple c (σ.trans τ.symm))),
    (σ.trans τ.symm).trans (Program.reassign (imageTuple c (π.trans τ)) (imageTuple c (σ.trans τ.symm))).symm) = _
  rw [forward,inverse,Program.reassign_symm]
  exact Prod.ext (Equiv.ext fun _ => τ.symm_apply_apply _) (Equiv.ext fun _ => τ.apply_symm_apply _)

/-- Marginal preservation with a second full permutation, which can later
be conditioned on the measured message. -/
theorem programmed_law (S : Sha2Set) (k : S.Node) (B : Permutation → ℝ≥0∞) :
    uniformMean B = uniformMean (fun π => uniformMean (fun σ => B (programmed S k π σ))) := by
  let T := column S k
  let e := Function.Involutive.toPerm _ (exchange_inv T)
  have h := Classic.mean_equiv e (fun p : Permutation × Permutation => B p.1)
  simp only [Classic.mean_prod] at h
  have const (π : Permutation) : uniformMean (fun _ : Permutation => B π) = B π := by
    simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
  simp_rw [const] at h
  exact h.symm

private theorem commute {T U : Type} [Fintype T] [Fintype U] (v : T → U → ℝ≥0∞) :
    uniformMean (fun t => uniformMean (v t)) = uniformMean (fun u => uniformMean (fun t => v t u)) := by
  simp only [uniformMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => mul_left_comm ..

private theorem mean_bound {B : Type} [Fintype B] [Nonempty B] (f g : B → ℝ≥0∞) (ε : ℝ≥0∞)
    (h : ∀ b, f b ≤ g b+ε) : uniformMean f ≤ uniformMean g+ε := by
  apply (Finset.sum_le_sum (s:=Finset.univ) fun b _ => mul_le_mul' (le_rfl : unifW B b ≤ _) (h b)).trans_eq
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,sum_unifW,one_mul,uniformMean]

variable (S : Sha2Set) {E Z : Type} [Fintype E] [DecidableEq E]
/-- In the original real experiment the secret k may determine every
operation after the cut. Introduce a uniform replacement column exactly
and then change the public prefix to the common reference permutation. -/
theorem real_public_switch (pre : (Port → Words) → Closed (WS Port Words E) Z)
    (hp : PUE (spec:=unifSpec) cnt0 pre (2^41))
    (post : S.Node → Permutation → Z → Closed (WS Port Words E) Bool)
    (M : Matrix (WS Port Words E) (WS Port Words E) ℂ) (pos : M.PosSemidef) (one : M.trace.re ≤ 1) :
    uniformMean (fun π : Permutation => uniformMean (fun k : S.Node =>
      qWeight (· = true) (pre (oracle π) >>= post k π) M)) ≤
    uniformMean (fun π : Permutation => uniformMean (fun σ : Permutation => uniformMean (fun k : S.Node =>
      qWeight (· = true) (pre (oracle π) >>= post k (programmed S k π σ)) M))) + ((2:ℝ≥0∞)^19)⁻¹ := by
  let test (k : S.Node) (π : Permutation) := qWeight (· = true) (pre (oracle π) >>= post k π) M
  let out (π σ : Permutation) (k : S.Node) := qWeight (· = true)
    (pre (oracle π) >>= post k (programmed S k π σ)) M
  let ε : ℝ≥0∞ := ((2:ℝ≥0∞)^19)⁻¹
  have each (π σ) := programmed_prefix S π σ pre hp (fun k => post k (programmed S k π σ)) M pos one
  have shuffle :
      uniformMean (fun π => uniformMean (fun k => test k π)) =
      uniformMean (fun π => uniformMean (fun σ => uniformMean (fun k => test k (programmed S k π σ)))) := by
    rw [commute]
    have key (k) := programmed_law S k (test k)
    simp_rw [key]
    rw [commute]
    exact congrArg uniformMean (funext fun π => commute _)
  have bound (π) : uniformMean (fun σ => uniformMean (fun k => test k (programmed S k π σ))) ≤
      uniformMean (fun σ => uniformMean (out π σ)) + ε := by
    exact mean_bound _ _ ε (each π)
  change uniformMean (fun π => uniformMean (fun k => test k π)) ≤ _
  rw [shuffle]
  exact mean_bound _ _ ε bound

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.real_public_switch
