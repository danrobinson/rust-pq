import Integration.SlhDsaShakePermutationRegular

namespace Reduction.ShakePermutation
open ENNReal

/-- Independent rate mask attached to a completed capacity path. -/
abbrev RateMask := Capacity → Rate

def rateXor (a b : Rate) : Rate := fun i => a i ^^^ b i

@[simp] theorem rateXor_cancel (a b : Rate) : rateXor (rateXor a b) b = a := by
  funext i
  simp [rateXor,UInt64.xor_assoc]

def shear (h : RateMask) (w : Words) : Words :=
  join (rateXor (rateOf w) (h (capOf w))) (capOf w)

@[simp] theorem shear_shear (h : RateMask) (w : Words) : shear h (shear h w) = w := by
  simp only [shear,rate_join,cap_join,rateXor_cancel,join_split]

def shearEquiv (h : RateMask) : Permutation := Function.Involutive.toPerm (shear h) (shear_shear h)

/-- The three random functions used by the compressed simulator can be
introduced without changing the distribution of the shared two-way round. -/
def salted (kin kout : Mask) (h : RateMask) (π : Permutation) : Permutation :=
  (masked kin kout π).trans (shearEquiv h)

theorem oracle_salted (kin kout : Mask) (h : RateMask) (π : Permutation) (d : Bool) (w : Words) :
    oracle (salted kin kout h π) (d,w) =
      if d then mask kin (π.symm (mask kout (shear h w))) else
        shear h (mask kout (π (mask kin w))) := by
  cases d <;> rfl

theorem uniform_salted (kin kout : Mask) (h : RateMask) (f : Permutation → ℝ≥0∞) :
    (∑ π : Permutation, (Fintype.card Permutation : ℝ≥0∞)⁻¹ * f (salted kin kout h π)) =
      ∑ π : Permutation, (Fintype.card Permutation : ℝ≥0∞)⁻¹ * f π := by
  unfold salted
  rw [uniform_masked kin kout (fun π => f (π.trans (shearEquiv h)))]
  let e : Equiv.Perm Permutation := {
    toFun := fun π => π.trans (shearEquiv h)
    invFun := fun π => π.trans (shearEquiv h)
    left_inv := fun π => by apply Equiv.ext; intro w; exact shear_shear h _
    right_inv := fun π => by apply Equiv.ext; intro w; exact shear_shear h _ }
  exact Equiv.sum_comp e (fun π => (Fintype.card Permutation : ℝ≥0∞)⁻¹ * f π)

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.uniform_salted
