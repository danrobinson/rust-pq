import Integration.SlhDsaShakePermutationPairs

namespace Reduction.ShakePermutation
open Classical

private theorem union_card {A : Type} [Fintype A] (p q : A → Prop) :
    Nat.card {a // p a ∨ q a} ≤ Nat.card {a // p a} + Nat.card {a // q a} := by
  classical
  let f (a : {a // p a ∨ q a}) : {a // p a} ⊕ {a // q a} :=
    if h : p a.val then .inl ⟨a.val,h⟩ else .inr ⟨a.val,a.prop.resolve_left h⟩
  have back (a : {a // p a ∨ q a}) : Sum.elim Subtype.val Subtype.val (f a) = a.val := by
    simp only [f]; split <;> rfl
  have inject : Function.Injective f := fun a b h => Subtype.ext <|
    (back a).symm.trans ((congrArg (Sum.elim Subtype.val Subtype.val) h).trans (back b))
  simpa only [Nat.card_sum] using Nat.card_le_card_of_injective f inject

/-- Either exceptional predicate can be charged to one event under the actual
uniform ideal permutation. -/
theorem atypical_count :
    2^698 * Nat.card {π : Permutation // irregular π ∨ Pairs.exceptional π} ≤ Nat.card Permutation := by
  have b := union_card irregular Pairs.exceptional
  have x := irregular_probability
  have y := Pairs.exceptional_probability
  omega

theorem exists_typical : ∃ π : Permutation, ¬irregular π ∧ ¬Pairs.exceptional π := by
  classical
  by_contra! all
  have h (π : Permutation) : irregular π ∨ Pairs.exceptional π := Classical.or_iff_not_imp_left.mpr (all π)
  let e : Permutation ≃ {π : Permutation // irregular π ∨ Pairs.exceptional π} :=
    ⟨fun x => ⟨x,h x⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  have eq := Nat.card_congr e
  have count := atypical_count
  have pos : 0 < Nat.card Permutation := Nat.card_pos
  omega

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.atypical_count
#print axioms Reduction.ShakePermutation.exists_typical
