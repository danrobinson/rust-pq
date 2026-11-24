import Integration.SlhDsaShakePermutationLongHarmonic
import Integration.SlhDsaShakePermutationLongGram

/-! Orthogonality to lower-degree restrictions. Complete the coordinates
whose edges are not already in the conditioning trace. For harmonic
coefficients both ends can be summed inside the trace instead. If the
trace has fewer input labels than the coefficient degree, every remaining
term has a repeated source and vanishes. -/
namespace Reduction.ShakePermutation.Long.Harmonic
open Finset
set_option linter.unusedSectionVars false
noncomputable section
variable {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem box_zero (s : Finset A) (f : (I → A) → ℂ) (x : I → A) (is : List I)
    (outside : ∀ i ∉ is, x i ∈ s) (zero : ∀ v : I → A, (∀ i, v i ∈ s) → f v = 0) :
    sumBox (fun _ => s) f x is = 0 := by
  induction is generalizing x with
  | nil => exact zero x (fun i => outside i (by simp))
  | cons i js ih =>
    simp only [sumBox]
    apply Finset.sum_eq_zero; intro a ha
    apply ih; intro j nj
    by_cases same : j = i
    · simpa [same] using ha
    · rw [Function.update_of_ne same]; exact outside _ (by simp [same,nj])

theorem no_injection (s : Finset A) (small : s.card < Fintype.card I)
    (x : I → A) (bounded : ∀ i, x i ∈ s) : ¬Function.Injective x := by
  intro inj
  let f : I → s := fun i => ⟨x i,bounded i⟩
  have h : Function.Injective f := fun _ _ eq => inj (congrArg Subtype.val eq)
  simpa only [Fintype.card_coe,not_le.mpr small] using Fintype.card_le_of_injective f h

theorem lower_box (s : Finset A) (t : Finset B) (f : (I → A) → (I → B) → ℂ)
    (is : List I) (distinct : is.Nodup) (left : ∀ i ∈ is, ∀ y, zeroMarginal (fun x => f x y) i)
    (right : ∀ i ∈ is, ∀ x, zeroMarginal (f x) i) (zero : ∀ x y, ¬Function.Injective x → f x y = 0)
    (small : s.card < Fintype.card I) (x : I → A) (y : I → B) (outside : ∀ i ∉ is, x i ∈ s) :
    sumBox (fun _ => tᶜ) (fun v => sumBox (fun _ => sᶜ) (fun u => f u v) x is) y is = 0 := by
  have switch := two_ends (fun _ : I => sᶜ) (fun _ : I => tᶜ) f is distinct left right x y
  simp only [compl_compl] at switch
  rw [switch]
  have inner (v : I → B) := box_zero s (fun u => f u v) x is outside
    (fun u h => zero u v (no_injection s small u h))
  simp_rw [inner]
  suffices ∀ (js : List I) (z : I → B), sumBox (fun _ => t) (fun _ => 0) z js = 0 from this is y
  intro js; induction js with
  | nil => exact fun _ => rfl
  | cons i js ih => intro z; simp [sumBox,ih]

end
end Reduction.ShakePermutation.Long.Harmonic
#print axioms Reduction.ShakePermutation.Long.Harmonic.lower_box
