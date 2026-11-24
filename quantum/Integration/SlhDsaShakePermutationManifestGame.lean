import Integration.SlhDsaShakePermutationManifestRisk
import Integration.SlhDsaShakeXofTcr

/-! Quantum transfer for experiments whose private overwrite paths belong to
a predetermined prefix tree. The test receives the whole two-way permutation
and every path output together. -/
namespace Reduction.ShakePermutation.Manifest
open Classical Quantum SetOracle Fix ENNReal
set_option maxRecDepth 8192
noncomputable section

private theorem swapMean {A B : Type} [Fintype A] [Fintype B] (u : A → B → ℝ≥0∞) :
    uniformMean (fun a => uniformMean (u a)) = uniformMean (fun b => uniformMean (fun a => u a b)) := by
  simp only [uniformMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..

private theorem uniform_shear (h : RateMask) (v : Permutation → ℝ≥0∞) :
    uniformMean (fun π : Permutation => v (π.trans (shearEquiv h))) = uniformMean v := by
  let e : Equiv.Perm Permutation := {
    toFun π := π.trans (shearEquiv h)
    invFun π := π.trans (shearEquiv h)
    left_inv π := Equiv.ext fun _ => shear_shear h _
    right_inv π := Equiv.ext fun _ => shear_shear h _ }
  exact Equiv.sum_comp e (fun π => (Fintype.card Permutation : ℝ≥0∞)⁻¹ * v π)

variable {I : Type} [Fintype I] [DecidableEq I]

def simulator (t : Tree I) (π : Permutation) (h : RateMask) (f : I → Rate) : Permutation :=
  if safe : good t π then π.trans (shearEquiv
    (program ⟨_,safe.1⟩ (fun i => rateOf (overwrite π (t.paths i))) h f))
  else π.trans (shearEquiv h)

private theorem badMass {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p] :
    uniformMean (fun a => if p a then (0 : ℝ≥0∞) else 1) =
      (Fintype.card {a // ¬ p a} : ℝ≥0∞) / Fintype.card A := by
  classical
  rw [uniformMean,← Fintype.sum_subtype_add_sum_subtype p]
  have yes (a : {a // p a}) : p a.val := a.property
  have no (a : {a // ¬ p a}) : ¬ p a.val := a.property
  simp only [ite_eq_left (yes _),ite_eq_right (no _),mul_zero,mul_one,Finset.sum_const_zero,zero_add,
    unifW,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,div_eq_mul_inv]

private theorem fraction (bad total n : ℕ) (ht : 0 < total) (h : 2^512 * bad ≤ n^2 * total) :
    (bad : ℝ≥0∞)/total ≤ (n : ℝ≥0∞)^2/2^512 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  rw [div_le_div_iff₀ (by exact_mod_cast ht) (by positivity)]
  rw [mul_comm (bad : ℝ)]
  exact_mod_cast h

/-- A uniformly chosen real permutation with all predetermined overwrite
outputs is within n²/2^512 (one-sided) of a simulated whole permutation and
an independently sampled full output table f. The quantum test can select
paths adaptively inside the fixed tree; the tree itself is independent of π. -/
theorem game (t : Tree I) (ncap : Nat.card I ≤ 2^512)
    (W : Permutation → (I → Rate) → ℝ≥0∞) (bounded : ∀ π f, W π f ≤ 1) :
    uniformMean (fun π : Permutation => W π (fun i => rateOf (overwrite π (t.paths i)))) ≤
      uniformMean (fun π : Permutation => uniformMean (fun h => uniformMean (fun f => W (simulator t π h f) f))) +
        (Nat.card I : ℝ≥0∞)^2/2^512 := by
  let real (π : Permutation) := W π (fun i => rateOf (overwrite π (t.paths i)))
  let ideal (π : Permutation) := uniformMean (fun h => uniformMean (fun f => W (simulator t π h f) f))
  have mix : uniformMean real = uniformMean (fun π : Permutation => uniformMean
      (fun h => real (π.trans (shearEquiv h)))) := by
    rw [swapMean]
    change uniformMean real = uniformMean (fun h => uniformMean (fun π : Permutation => real (π.trans (shearEquiv h))))
    simp_rw [uniform_shear]
    simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
  have ne (i : I) : t.paths i ≠ [] := by rw [t.step i]; simp
  have per (π : Permutation) : uniformMean (fun h => real (π.trans (shearEquiv h))) ≤
      ideal π + (if good t π then 0 else 1) := by
    by_cases ok : good t π
    · rw [ite_eq_left ok,add_zero]
      simpa only [real,ideal,simulator,dite_eq_left ok] using (whole_port π t.paths ne ok.1 W).le
    · rw [ite_eq_right ok]
      apply le_trans (b := 1) (ShakeXof.mean_le_const (fun _ => bounded _ _))
      exact le_add_self
  have h := Finset.sum_le_sum (s := Finset.univ) (fun π _ => mul_le_mul' (le_refl (unifW _ π)) (per π))
  change uniformMean real ≤ uniformMean ideal + _
  rw [mix]
  apply le_trans h
  simp only [mul_add, Finset.sum_add_distrib]
  apply add_le_add le_rfl
  change uniformMean (fun a => if good t a then 0 else 1) ≤ _
  rw [badMass]
  exact fraction _ _ _ Fintype.card_pos (by simpa only [Nat.card_eq_fintype_card] using missing_count t ncap)

end
end Reduction.ShakePermutation.Manifest
#print axioms Reduction.ShakePermutation.Manifest.game
