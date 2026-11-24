import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Cancellation of the unmatched coordinates in the completion-state
Gram operator. Coefficients on non-injective tuples are extended by zero,
so each vanishing marginal is a sum over the whole coordinate alphabet. -/
namespace Reduction.ShakePermutation.Long.Harmonic
open Finset
variable {I A B : Type} [DecidableEq I] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
set_option linter.unusedSectionVars false
noncomputable section

def sumBox (domain : I → Finset A) (f : (I → A) → ℂ) (x : I → A) : List I → ℂ
  | [] => f x
  | i :: is => ∑ a ∈ domain i, sumBox domain f (Function.update x i a) is

def zeroMarginal (f : (I → A) → ℂ) (i : I) := ∀ x, ∑ a, f (Function.update x i a) = 0

theorem marginal_box (domain : I → Finset A) (f : (I → A) → ℂ) (i : I)
    (z : zeroMarginal f i) (is : List I) (fresh : i ∉ is) (x : I → A) :
    ∑ a, sumBox domain f (Function.update x i a) is = 0 := by
  induction is generalizing x with
  | nil => exact z x
  | cons j js ih =>
    have ne : i ≠ j := fun e => fresh (List.mem_cons.mpr (.inl e))
    have miss : i ∉ js := fun h => fresh (List.mem_cons_of_mem j h)
    simp only [sumBox]
    rw [Finset.sum_comm]
    simp only [Function.update_comm ne,ih miss,Finset.sum_const_zero]

/-- Summing the harmonic coordinates outside a set equals summing them
inside, with one minus sign for each switched coordinate. -/
theorem complement (domain : I → Finset A) (f : (I → A) → ℂ) (is : List I) (nodup : is.Nodup)
    (h : ∀ i ∈ is, zeroMarginal f i) (x : I → A) :
    sumBox domain f x is = (-1 : ℂ)^is.length * sumBox (fun i => (domain i)ᶜ) f x is := by
  induction is generalizing x with
  | nil => simp [sumBox]
  | cons i is ih =>
    have fresh := (List.nodup_cons.mp nodup).1
    have rest := (List.nodup_cons.mp nodup).2
    have hz := marginal_box (fun j => (domain j)ᶜ) f i (h i (by simp)) is fresh x
    let g (a : A) := sumBox (fun j => (domain j)ᶜ) f (Function.update x i a) is
    have split : (∑ a ∈ domain i, g a) + (∑ a ∈ (domain i)ᶜ, g a) = 0 :=
      (sum_add_sum_compl (domain i) g).trans hz
    have s : (∑ a ∈ domain i, g a) = -(∑ a ∈ (domain i)ᶜ, g a) := eq_neg_of_add_eq_zero_left split
    simp only [sumBox,ih rest (fun j hj => h j (List.mem_cons_of_mem i hj)),← Finset.mul_sum,List.length_cons,pow_succ]
    change (-1:ℂ)^is.length * (∑ a ∈ domain i, g a) = _ * (∑ a ∈ (domain i)ᶜ, g a)
    rw [s]; ring

private theorem sumBox_weight (d : I → Finset A) (f : (I → A) → ℂ) (k : ℂ) (x : I → A) (is : List I) :
    sumBox d (fun x => k*f x) x is = k*sumBox d f x is := by
  induction is generalizing x with
  | nil => rfl
  | cons i js ih => simp only [sumBox,ih,Finset.mul_sum]

/-- Switching both ends of each unmatched edge cancels the signs. This
turns the two unrestricted outside sums in a Gram row into sums indexed
only by the old domain and image labels. -/
theorem two_ends (d : I → Finset A) (e : I → Finset B) (f : (I → A) → (I → B) → ℂ)
    (is : List I) (hi : is.Nodup) (left : ∀ i ∈ is, ∀ y, zeroMarginal (fun x => f x y) i)
    (right : ∀ i ∈ is, ∀ x, zeroMarginal (f x) i) (x : I → A) (y : I → B) :
    sumBox e (fun y => sumBox d (fun x => f x y) x is) y is =
      sumBox (fun j => (e j)ᶜ) (fun y => sumBox (fun j => (d j)ᶜ) (fun x => f x y) x is) y is := by
  have swapBox (d : I → Finset A) (e : I → Finset B) (xs ys : List I) (x : I → A) (y : I → B) :
      sumBox e (fun z => sumBox d (fun v => f v z) x xs) y ys =
      sumBox d (fun v => sumBox e (f v) y ys) x xs := by
    have add {K : Type} (s : Finset K) (g : K → (I → A) → ℂ) (v : I → A) (ix : List I) :
        sumBox d (fun u => ∑ k ∈ s, g k u) v ix = ∑ k ∈ s, sumBox d (g k) v ix := by
      induction ix generalizing v with
      | nil => rfl
      | cons i is ih => simpa only [sumBox,ih] using Finset.sum_comm
    induction ys generalizing y with
    | nil => rfl
    | cons i js ih => simp only [sumBox,ih,add]
  rw [swapBox]
  simp_rw [complement e _ is hi (fun i h => right i h _)]
  rw [sumBox_weight,← swapBox]
  simp_rw [complement d _ is hi (fun i h => left i h _)]
  rw [sumBox_weight,← mul_assoc,← mul_pow]
  simp

end
end Reduction.ShakePermutation.Long.Harmonic
#print axioms Reduction.ShakePermutation.Long.Harmonic.two_ends
