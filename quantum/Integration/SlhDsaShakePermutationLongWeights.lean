import Integration.SlhDsaShakePermutationLongPermKernel
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-! The total mass of all nondiagonal positive completion kernels is
small. The estimate allows both orientations and all coordinate
permutations within a selected subset. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Finset
noncomputable section

def weight (N r j : ℕ) : ℝ := ((N-r-j).factorial : ℝ) / (N-r).factorial

theorem support_card {r : ℕ} (H : Finset (Fin r)) :
    Fintype.card {w : Equiv.Perm (Fin r) // permutes H w} = H.card.factorial := by
  calc _ = Fintype.card (Equiv.Perm H) := by
          apply Fintype.card_congr
          exact (Equiv.Perm.subtypeEquivSubtypePerm (fun i => i ∈ H)).symm
       _ = _ := by rw [Fintype.card_perm,Fintype.card_coe]

theorem weight_bound (N r j : ℕ) (size : 3*r+1 ≤ N) (hj : j ≤ r) :
    (r.choose j : ℝ) * ((j.factorial : ℝ) * weight N r j) ≤ ((r : ℝ) / (N-2*r : ℕ))^j := by
  have pos : 0 < N-2*r := by omega
  have h1 := Nat.descFactorial_le_pow r j
  have h2 := (Nat.pow_le_pow_left (show N-2*r ≤ N-r+1-j from by omega) j).trans (Nat.pow_sub_le_descFactorial (N-r) j)
  have h3 := Nat.factorial_mul_descFactorial (show j ≤ N-r from by omega)
  have h4 := Nat.descFactorial_eq_factorial_mul_choose r j
  rw [weight,div_pow]
  have den1 : 0 < ((N-r).factorial : ℝ) := by positivity
  have den2 : 0 < ((N-2*r : ℕ):ℝ)^j := by positivity
  rw [← mul_div_assoc,← mul_div_assoc,div_le_div_iff₀ den1 den2]
  have h : r.choose j * (j.factorial * (N-r-j).factorial) * (N-2*r)^j ≤ r^j * (N-r).factorial := by
    calc _ = r.descFactorial j * ((N-r-j).factorial * (N-2*r)^j) := by rw [h4]; ring
         _ ≤ r^j * ((N-r-j).factorial * (N-r).descFactorial j) := Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ h2)
         _ = _ := by rw [h3]
  exact_mod_cast h

theorem total_weight (N r : ℕ) (size : 3*r+1 ≤ N) :
    (∑ H : Finset (Fin r), if H = ∅ then 0 else
        (Fintype.card {w : Equiv.Perm (Fin r) // permutes H w} : ℝ) * weight N r H.card)
      ≤ (r : ℝ) * ((r : ℝ) / (N-2*r : ℕ)) := by
  let c (j : ℕ) : ℝ := if j=0 then 0 else j.factorial * weight N r j
  have e (H : Finset (Fin r)) :
      (if H = ∅ then 0 else (Fintype.card {w : Equiv.Perm (Fin r) // permutes H w} : ℝ) * weight N r H.card) = c H.card := by
    simp [c,support_card]
  simp_rw [e]
  rw [← Finset.powerset_univ,Finset.sum_powerset_apply_card]
  simp only [card_univ,Fintype.card_fin,Finset.sum_range_succ',c,ite_true,mul_zero,add_zero,
    Nat.succ_ne_zero,ite_false,nsmul_eq_mul]
  have d : 0 < N-2*r := by omega
  have one : (r:ℝ) / (N-2*r : ℕ) ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast (show r ≤ N-2*r from by omega))
  calc _ ≤ ∑ _j ∈ range r, ((r : ℝ)/(N-2*r : ℕ)) := by
         apply Finset.sum_le_sum; intro j hj
         exact (weight_bound N r (j+1) size (Finset.mem_range.mp hj)).trans
           (by simpa using pow_le_pow_of_le_one (by positivity : 0 ≤ (r:ℝ)/(N-2*r:ℕ)) one (show 1 ≤ j+1 by omega))
       _ = _ := by simp

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.total_weight
