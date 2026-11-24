import Integration.SlhDsaShakePermutationLongLower

/-! Expanding a coordinate box as an ordinary finite sum, including
frozen coordinates. This lets the two-sided harmonic cancellation act
on entries of the actual permutation completion Gram matrix. -/
namespace Reduction.ShakePermutation.Long.Harmonic
set_option linter.unusedSectionVars false
open Finset Classical
noncomputable section
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

def inside (s : I → Finset A) (is : List I) (x u : I → A) : Prop :=
  (∀ i ∈ is, u i ∈ s i) ∧ ∀ i ∉ is, u i = x i

theorem inside_cons (s : I → Finset A) (i : I) (js : List I) (fresh : i ∉ js) (x u : I → A)
    (a : A) : a ∈ s i ∧ inside s js (Function.update x i a) u ↔ inside s (i::js) x u ∧ a = u i := by
  unfold inside
  constructor
  · rintro ⟨ha,mem,freeze⟩
    have eq : u i = a := (freeze i fresh).trans (Function.update_self ..)
    refine ⟨⟨?_,?_⟩,eq.symm⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl|h
      · rwa [eq]
      · exact mem _ h
    · intro j hj
      have ne : j ≠ i := fun h => hj (List.mem_cons.mpr (.inl h))
      exact (freeze _ (fun h => hj (List.mem_cons_of_mem _ h))).trans (Function.update_of_ne ne ..)
  · rintro ⟨⟨mem,freeze⟩,rfl⟩
    refine ⟨mem _ (List.mem_cons_self ..),fun j hj => mem _ (List.mem_cons_of_mem _ hj),?_⟩
    intro j hj
    by_cases h : j=i
    · simp [h]
    · rw [Function.update_of_ne h]; exact freeze _ (by simp [h,hj])

theorem expand (s : I → Finset A) (f : (I → A) → ℂ) (is : List I) (hi : is.Nodup) (x : I → A) :
    sumBox s f x is = ∑ u, if inside s is x u then f u else 0 := by
  induction is generalizing x with
  | nil =>
    have h (u : I → A) : inside s [] x u ↔ u = x := by simp [inside,funext_iff]
    simp [sumBox,h]
  | cons i js ih =>
    have fresh := (List.nodup_cons.mp hi).1
    simp only [sumBox,ih (List.nodup_cons.mp hi).2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    change ∑ a ∈ s i, (if inside s js (Function.update x i a) u then f u else 0) = _
    rw [← Finset.sum_filter]
    by_cases good : inside s (i::js) x u
    · have h : (s i).filter (fun a => inside s js (Function.update x i a) u) = {u i} := by
        ext a; simp only [Finset.mem_filter,Finset.mem_singleton,inside_cons s i js fresh,good,true_and]
      simp [h,good]
    · have h : (s i).filter (fun a => inside s js (Function.update x i a) u) = ∅ := by
        ext a; simp only [Finset.mem_filter,Finset.notMem_empty,inside_cons s i js fresh,good,false_and]
      simp [h,good]

end
end Reduction.ShakePermutation.Long.Harmonic
#print axioms Reduction.ShakePermutation.Long.Harmonic.expand
