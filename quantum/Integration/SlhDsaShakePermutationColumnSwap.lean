import Integration.SlhDsaShakePermutationResample

namespace Reduction.ShakePermutation.Program
open Classical
variable {I J : Type} (a : I × J → Words) (π : Permutation) (t : I × J → Words)
variable (ok : Function.Injective (pair a π t))

def labelled : (I × Bool × J) ↪ Words where
  toFun s := pair a π t (s.2.1,s.1,s.2.2)
  inj' _ _ e := by obtain ⟨b,k,j⟩ := Prod.ext_iff.mp (ok e) |>.imp_right Prod.ext_iff.mp; exact Prod.ext k (Prod.ext b j)

theorem resample_column (k : I) :
    resample (fun j => a (k,j)) (π,fun j => t (k,j)) =
      (changed π (labelled a π t ok) k,fun j => π (a (k,j))) := by
  let f := column (labelled a π t ok) k
  have eq : pair (fun j => a (k,j)) π (fun j => t (k,j)) = f := by
    funext s
    rcases s with ⟨b,j⟩
    cases b <;> rfl
  have inject := eq ▸ f.injective
  simp only [resample,dite_eq_left inject,changed]
  have same : (⟨_,inject⟩ : (Bool × J) ↪ Words) = f := DFunLike.ext _ _ (congrFun eq)
  rw [same]
  rfl

include ok in
theorem resampled_output (k : I) (j : J) :
    (resample (fun j => a (k,j)) (π,fun j => t (k,j))).1 (a (k,j)) = t (k,j) := by
  rw [resample_column a π t ok k]
  exact changed_hit π (labelled a π t ok) k j _ rfl

end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.resampled_output
