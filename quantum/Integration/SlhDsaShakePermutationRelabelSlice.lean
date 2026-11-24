import VCVio.Quantum.Oracle.Compressed.Action

/-! A test for a mask-query hybrid on correlated recording databases.  The
coefficient keeps the other database registers, including the path register,
so contributions from different mask values can interfere. -/
namespace Reduction.ShakePermutation.RelabelSlice
open Quantum
variable {Y D : Type} [Fintype Y] [DecidableEq Y] [DecidableEq D]

/-- One matrix element of the commutator of local mask compression with a
mask-controlled relabeling, between an occupied and an empty mask cell. -/
noncomputable def coefficient (v : Option Y → Equiv.Perm D) (y : Y) (d out : D) : ℂ :=
  cellCompress Y none (some y) *
    ((if v (some y) d = out then 1 else 0) - (if v none d = out then 1 else 0))

/-- If relabeling routes a different occupied cell in every branch to one
common output, and cannot do that for the empty mask, these amplitudes add.
Weights are those of the uniform superposition before projection onto s. -/
theorem coherent_coefficient (s : Finset Y) (d : Y → D) (out : D)
    (v : Option Y → Equiv.Perm D) (hit : ∀ y ∈ s, v (some y) (d y) = out)
    (miss : ∀ y ∈ s, v none (d y) ≠ out) :
    ∑ y ∈ s, cellAmp Y * coefficient v y (d y) out =
      (s.card : ℂ) / Fintype.card Y := by
  classical
  calc
    _ = ∑ _y ∈ s, (Fintype.card Y : ℂ)⁻¹ := Finset.sum_congr rfl fun y hy => by
      simp [coefficient,hit y hy,miss y hy,cellAmp_mul_self]
    _ = _ := by simp [div_eq_mul_inv]

end Reduction.ShakePermutation.RelabelSlice
#print axioms Reduction.ShakePermutation.RelabelSlice.coherent_coefficient
