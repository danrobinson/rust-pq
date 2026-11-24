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

/-- Local compression, tensored with identity on all other recording cells. -/
noncomputable def compress (w : Option Y → D → ℂ) (b : Option Y) (x : D) : ℂ :=
  ∑ a, cellCompress Y b a * w a x

/-- Move basis states by the mask-controlled cell permutation. -/
def relabel (v : Option Y → Equiv.Perm D) (w : Option Y → D → ℂ) (b : Option Y) (x : D) : ℂ :=
  w b ((v b).symm x)

noncomputable def correlated (s : Finset Y) (d : Y → D) : Option Y → D → ℂ
  | none, _ => 0
  | some y, x => if y ∈ s ∧ x = d y then cellAmp Y else 0

theorem commutator_component (s : Finset Y) (d : Y → D) (out : D) (v : Option Y → Equiv.Perm D) :
    compress (relabel v (correlated s d)) none out -
        relabel v (compress (correlated s d)) none out =
      ∑ y ∈ s, cellAmp Y * coefficient v y (d y) out := by
  classical
  simp only [compress,relabel,Fintype.sum_option,correlated,mul_zero,zero_add,← Finset.sum_sub_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ s)]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  have off : ∀ y ∈ Finset.univ.filter (fun y => y ∉ s),
      cellCompress Y none (some y) * (if y ∈ s ∧ (v (some y)).symm out = d y then cellAmp Y else 0) -
      cellCompress Y none (some y) * (if y ∈ s ∧ (v none).symm out = d y then cellAmp Y else 0) = 0 := by
    intro y hy
    simp [(Finset.mem_filter.mp hy).2]
  rw [Finset.sum_eq_zero off,add_zero]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [hy,true_and,Equiv.symm_apply_eq,coefficient]
  simp only [eq_comm (a:=out) (b:=v (some y) (d y)),eq_comm (a:=out) (b:=v none (d y))]
  by_cases h : v (some y) (d y) = out <;> by_cases h' : v none (d y) = out <;>
    simp [h,h',cellCompress_none_some]

theorem correlated_mass [Fintype D] (s : Finset Y) (d : Y → D) :
    ∑ b, ∑ x, Complex.normSq (correlated s d b x) =
      (s.card : ℝ) / Fintype.card Y := by
  classical
  rw [Fintype.sum_option]
  simp only [correlated,Complex.normSq_zero,Finset.sum_const_zero,zero_add]
  have each (y : Y) : (∑ x : D, Complex.normSq (if y ∈ s ∧ x = d y then cellAmp Y else 0)) =
      if y ∈ s then (Fintype.card Y : ℝ)⁻¹ else 0 := by
    by_cases hy : y ∈ s <;> simp [hy,apply_ite,cellAmp,Nat.cast_nonneg]
  simp only [each,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

end Reduction.ShakePermutation.RelabelSlice
#print axioms Reduction.ShakePermutation.RelabelSlice.coherent_coefficient
#print axioms Reduction.ShakePermutation.RelabelSlice.commutator_component
#print axioms Reduction.ShakePermutation.RelabelSlice.correlated_mass
