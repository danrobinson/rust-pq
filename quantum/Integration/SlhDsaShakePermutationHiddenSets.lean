import Integration.SlhDsaShakePermutationHiddenQueries

namespace Reduction.ShakePermutation.Hidden
open Classical Quantum
set_option maxRecDepth 8192
variable {I E : Type} [Fintype I] [Fintype E]
variable {C : Type} [DecidableEq C] (π : Permutation) (g : I → Permutation) (addr : Port → C)
variable (rows : I → Finset C) (b : ℕ)
variable (outside : ∀ i p, addr p ∉ rows i → oracle (g i) p = oracle π p)
variable (overlap : ∀ z, (Finset.univ.filter fun i => z ∈ rows i).card ≤ b)

include outside in
private theorem row_mass (p : Port) (ψ : Port → Words × E → ℂ) (i : I) :
    ∑ w, ‖after (g i) ψ p w - after π ψ p w‖^2 ≤
      if addr p ∈ rows i then 4*∑ w, ‖ψ p w‖^2 else 0 := by
  classical
  split
  · calc
      _ ≤ ∑ w, 2*(‖after (g i) ψ p w‖^2 +
          ‖after π ψ p w‖^2) := Finset.sum_le_sum fun w _ => sq_diff _ _
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib,fibers,fibers]; ring
  · rename_i miss
    have eq := outside i p miss
    simp only [after,eq,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,le_rfl]

include outside overlap in
theorem changed_call_sum (x : Vec E) :
    ∑ i, ‖call (g i) x - call π x‖^2 ≤
      (4*b)*‖x‖^2 := by
  classical
  simp only [norm_expand,PiLp.sub_apply]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  let ψ (p : Port) (w : Words × E) := x ((p,w.1),w.2)
  apply le_trans (Finset.sum_le_sum (fun i _ => row_mass π g addr rows outside p ψ i))
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_assoc, mul_left_comm]
  have bound : (((Finset.univ.filter fun i => addr p ∈ rows i).card : ℕ) : ℝ) ≤ b :=
    Nat.cast_le.mpr (overlap _)
  have pos : 0 ≤ ∑ w, ‖ψ p w‖^2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bound pos) (by norm_num)

variable (ki ko : Mask) (h : RateMask) (program : I → RateMask)
variable (caps : I → Finset Capacity) (multiplicity : ℕ)
variable (outsideCaps : ∀ i z, z ∉ caps i → program i z = h z)
variable (capBound : ∀ z, (Finset.univ.filter fun i => z ∈ caps i).card ≤ multiplicity)

include outsideCaps capBound in
/-- A hidden seed may determine many programmed capacities, even depending
on the private base permutation. The quantitative input is how many possible
seeds can select any one capacity, conditional on the base oracle. -/
theorem set_queries (op : ℕ → Vec E ≃ₗᵢ[ℂ] Vec E) (x : Vec E) (q : ℕ) :
    ∑ i, ‖interact (salted ki ko (program i) π) op x q - interact (salted ki ko h π) op x q‖^2 ≤
      4*multiplicity*(q:ℝ)^2*‖x‖^2 :=
  query_hybrid _ _ _ (changed_call_sum (salted ki ko h π) (fun i => salted ki ko (program i) π)
    (addressed π ki ko) caps multiplicity (fun i p miss => oracle_agrees _ _ _ _ _ p (outsideCaps i _ miss)) capBound) op x q

end Reduction.ShakePermutation.Hidden
#print axioms Reduction.ShakePermutation.Hidden.set_queries
