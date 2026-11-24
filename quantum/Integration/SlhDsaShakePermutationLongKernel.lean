import Integration.SlhDsaShakePermutationLongInside

/-! On harmonic coefficients the completion kernel reduces to a weighted
sum of coordinate replacement operators on the old matching. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Harmonic Finset OracleComp PermutationConditioning
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] {r : ℕ}

private theorem pull (D : Finset A) (p : Equiv.Perm A) (g : (Fin r → A) → ℂ)
    (support : ∀ u, (¬∀ i, p.symm (u i) ∈ D) → g u = 0) :
    ∑ u, g u = ∑ v : Fin r → D, g (fun i => p (v i).val) := by
  symm
  apply Fintype.sum_of_injective (fun (v : Fin r → D) i => p (v i).val)
    (fun _ _ he => funext (fun i => Subtype.ext (p.injective (congrFun he i)))) _ _ _ (fun _ => rfl)
  intro u outside; apply support u
  intro inside
  exact outside ⟨fun i => ⟨p.symm (u i),inside i⟩,funext (fun i => p.apply_symm_apply _)⟩

theorem restrict_cell {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (f : Coeff A r) :
    (∑ y, ∑ x, if closedFit p b x y then f x y else 0) =
      ∑ y : Fin r → D, ∑ x : Fin r → D, if closedFit p b (fun i => (x i).val) (fun i => p (y i).val)
        then f (fun i => (x i).val) (fun i => p (y i).val) else 0 := by
  rw [pull D p _ (fun y h => Finset.sum_eq_zero (fun x _ => ite_eq_right (fun fit => h (occupied fit).2)))]
  apply Finset.sum_congr rfl; intro y _
  apply pull D (Equiv.refl A)
  intro x h; exact ite_eq_right (fun fit => h (occupied fit).1)

theorem masks {D : Finset A} (p : Equiv.Perm A) (c : Finset (Fin r) → ℂ) (x y : Fin r → D) (z : ℂ) :
    (∑ b : Tag D r, c (holes b) * (if closedFit p b (fun i => (x i).val) (fun i => p (y i).val) then z else 0)) =
      ∑ H : Finset (Fin r), c H * (if ∀ i ∉ H, y i = x i then z else 0) := by
  let m (H : Finset (Fin r)) := mask H x
  have inj : Function.Injective m := fun H K h => (holes_mask H x).symm.trans ((congrArg holes h).trans (holes_mask K x))
  symm; apply Fintype.sum_of_injective m inj
  · intro b outside
    have ng : ¬closedFit p b (fun i => (x i).val) (fun i => p (y i).val) := by
      intro hit
      exact outside ⟨holes b,((mask_unique p b x y (holes b)).mp ⟨rfl,hit⟩).1.symm⟩
    simp [ng]
  · intro H
    have e := mask_unique p (m H) x y H
    simp only [m,holes_mask,true_and] at e
    simp [m,holes_mask,e]

def kernel {D : Finset A} (p : Equiv.Perm A) (f : Coeff A r) (H : Finset (Fin r)) :=
  ∑ y : Fin r → D, ∑ x : Fin r → D, if ∀ i ∉ H, y i = x i then
    f (fun i => (x i).val) (fun i => p (y i).val) else 0

theorem row_kernel (t : Trace A) (p : Extensions t) (f : Coeff A r)
    (sx : ∀ x y, ¬Function.Injective x → f x y = 0)
    (sy : ∀ x y, ¬Function.Injective y → f x y = 0)
    (left : ∀ i y, zeroMarginal (fun x => f x y) i) (right : ∀ i x, zeroMarginal (f x) i) :
    ∑ y, ∑ x, (count (t++pairs x y) : ℂ) * f x y =
      ∑ H : Finset (Fin r), ((Fintype.card A - (rank t + H.card)).factorial : ℂ) *
        kernel (D:=inputs t) p.val f H := by
  rw [row t p f sx sy]
  simp_rw [inside_cell p.val _ f left right,restrict_cell,kernel,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  exact masks p.val (fun H => ((Fintype.card A - (rank t + H.card)).factorial : ℂ)) x y _

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.row_kernel
