import Integration.SlhDsaShakePermutation

/-! Capacity masking for SHAKE256's ideal permutation, following the salted
permutation representation of Alagic, Carolan, Majenz and Tokat (2025).
Fixing both mask tables preserves the uniform law on the *whole* permutation,
so the identity applies jointly to the signer and the public two-way port. -/
namespace Reduction.ShakePermutation
open ENNReal

abbrev Rate := Fin 17 → UInt64
abbrev Capacity := Fin 8 → UInt64
abbrev Mask := Rate → Capacity

def rateOf (w : Words) : Rate := fun i => w ⟨i.val,by omega⟩

def mask (k : Mask) (w : Words) : Words := fun i =>
  if h : i.val < 17 then w i else w i ^^^ k (rateOf w) ⟨i.val-17,by omega⟩

@[simp] theorem rate_mask (k : Mask) (w : Words) : rateOf (mask k w) = rateOf w := by
  funext i
  simp [rateOf,mask,i.isLt]

@[simp] theorem mask_mask (k : Mask) (w : Words) : mask k (mask k w) = w := by
  funext i
  by_cases hi : i.val < 17
  · simp [mask,hi]
  · simp only [mask,hi,↓reduceDIte,rate_mask]
    simp [UInt64.xor_assoc]

def maskEquiv (k : Mask) : Permutation := Function.Involutive.toPerm (mask k) (mask_mask k)

/-- Independent masks can be used on the input and output of the permutation. -/
def masked (kin kout : Mask) (π : Permutation) : Permutation :=
  ((maskEquiv kin).trans π).trans (maskEquiv kout)

theorem oracle_masked (kin kout : Mask) (π : Permutation) (d : Bool) (w : Words) :
    oracle (masked kin kout π) (d,w) =
      if d then mask kin (π.symm (mask kout w)) else mask kout (π (mask kin w)) := by
  cases d <;> rfl

theorem masked_masked (kin kout : Mask) (π : Permutation) :
    masked kin kout (masked kin kout π) = π := by
  apply Equiv.ext
  intro w
  change mask kout (mask kout (π (mask kin (mask kin w)))) = π w
  simp

theorem uniform_masked (kin kout : Mask) (f : Permutation → ℝ≥0∞) :
    (∑ π : Permutation, (Fintype.card Permutation : ℝ≥0∞)⁻¹ * f (masked kin kout π)) =
      ∑ π : Permutation, (Fintype.card Permutation : ℝ≥0∞)⁻¹ * f π := by
  exact Equiv.sum_comp (Function.Involutive.toPerm (masked kin kout) (masked_masked kin kout))
    (fun π => (Fintype.card Permutation : ℝ≥0∞)⁻¹ * f π)

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.oracle_masked
#print axioms Reduction.ShakePermutation.uniform_masked
