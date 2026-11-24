import Shakebatch.WotsScatter

/-! The two passes of the linked chain-order routine count each digit and maintain its
next free output position. The bounded binary execution obligations are in wots_order.py. -/
open Aeneas.Std
namespace slhdsa.ShakeBatch.WotsOrder

def linkedSlot (digits : List U32) (i : Nat) :=
  let value := digits[i]!.val
  ((List.range value).map (counted digits digits.length)).sum + counted digits i value

private theorem prefixCounts (digits : List U32) (d : Nat) :
    ((List.range d).map (counted digits digits.length)).sum = below digits d := by
  induction d with
  | zero => simp [below]
  | succ d ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, below_next]
    simp

theorem linkedSlot_eq_rank (digits : List U32) (i : Nat) : linkedSlot digits i = rank digits i := by
  simp [linkedSlot,rank,prefixCounts]

theorem linkedSlot_bijective (digits : List U32) :
    ∃ f : Fin digits.length → Fin digits.length, Function.Bijective f ∧
      ∀ i, (f i).val = linkedSlot digits i.val := by
  let f : Fin digits.length → Fin digits.length := fun i => ⟨rank digits i.val,rank_lt digits i.val i.isLt⟩
  have inj : Function.Injective f := fun x y h =>
    Fin.ext (rank_injective digits x.isLt y.isLt (congrArg Fin.val h))
  exact ⟨f,⟨inj,Finite.surjective_of_injective inj⟩,fun i => (linkedSlot_eq_rank digits i).symm⟩

#print axioms linkedSlot_bijective
end slhdsa.ShakeBatch.WotsOrder
