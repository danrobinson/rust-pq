import Integration.SlhDsaShakePermutationLongCells

/-! Expansion of an actual permutation Gram row into harmonic boxes.
All cells of a row with too few preassigned edges vanish separately. -/
namespace Reduction.ShakePermutation.Long.Gram
open Classical Harmonic Finset OracleComp PermutationConditioning
noncomputable section
set_option linter.unusedSectionVars false
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] {r : ℕ}

abbrev Coeff (A : Type) (r : ℕ) := (Fin r → A) → (Fin r → A) → ℂ

def cell {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (f : Coeff A r) :=
  ∑ y, ∑ x, if fit p b x y then f x y else 0

theorem cell_box {D : Finset A} (p : Equiv.Perm A) (b : Tag D r) (f : Coeff A r) :
    cell p b f = sumBox (fun _ => (D.map p.toEmbedding)ᶜ)
      (fun v => sumBox (fun _ => Dᶜ) (fun u => f u v) (frozen b) (holes b).toList)
      (fun i => p (frozen b i)) (holes b).toList := by
  rw [expand _ _ _ (holes b).nodup_toList]
  apply Finset.sum_congr rfl; intro y _
  split <;> rename_i hy
  · rw [expand _ _ _ (holes b).nodup_toList]
    simp only [fit_box,hy,and_true]
  · simp only [fit_box,hy,and_false,ite_false,Finset.sum_const_zero]

theorem row (t : Trace A) (p : Extensions t) (f : Coeff A r)
    (sx : ∀ x y, ¬Function.Injective x → f x y = 0)
    (sy : ∀ x y, ¬Function.Injective y → f x y = 0) :
    ∑ y, ∑ x, (count (t++pairs x y) : ℂ) * f x y =
      ∑ b : Tag (inputs t) r, ((Fintype.card A - (rank t + (holes b).card)).factorial : ℂ) * cell p.val b f := by
  classical
  let c (b : Tag (inputs t) r) : ℂ := (Fintype.card A - (rank t + (holes b).card)).factorial
  change _ = ∑ b, c b * cell p.val b f
  unfold cell
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  by_cases hx : Function.Injective x
  · by_cases hy : Function.Injective y
    · rw [coefficient t p x y hx hy]
      simp only [fit_unique]
      by_cases h : admissible (inputs t) p.val x y
      · simp [h,c,holes_tag,mul_ite]
      · simp [h]
    · simp [sy x y hy]
  · simp [sx x y hx]

theorem row_lower (t : Trace A) (p : Extensions t) (f : Coeff A r)
    (sx : ∀ x y, ¬Function.Injective x → f x y = 0)
    (sy : ∀ x y, ¬Function.Injective y → f x y = 0)
    (left : ∀ i y, zeroMarginal (fun x => f x y) i)
    (right : ∀ i x, zeroMarginal (f x) i) (small : rank t < r) :
    ∑ y, ∑ x, (count (t++pairs x y) : ℂ) * f x y = 0 := by
  rw [row t p f sx sy]
  apply Finset.sum_eq_zero; intro b _
  rw [cell_box]
  suffices h : sumBox (fun _ => ((inputs t).map p.val.toEmbedding)ᶜ)
      (fun v => sumBox (fun _ => (inputs t)ᶜ) (fun u => f u v) (frozen b) (holes b).toList)
      (fun i => p.val (frozen b i)) (holes b).toList = 0 by rw [h,mul_zero]
  apply lower_box (inputs t) ((inputs t).map p.val.toEmbedding) f _ (holes b).nodup_toList
    (fun i _ => left i) (fun i _ => right i) sx (by simpa [rank] using small)
  intro i hi
  have ne : b i ≠ none := by simpa [holes] using hi
  obtain ⟨a,he⟩ := Option.ne_none_iff_exists'.mp ne
  simp [frozen,he]

end
end Reduction.ShakePermutation.Long.Gram
#print axioms Reduction.ShakePermutation.Long.Gram.row_lower
