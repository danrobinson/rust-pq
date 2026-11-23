import Shakebatch.WotsAdvance
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

theorem unequal_spec {width : Usize} (x y : Array U32 width) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU32 x y ⦃ b => (b=true ↔ x≠y) ⦄ := by
  unfold core.array.equality.PartialEqArray.ne
  have eq : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU32 x y =
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU32 x.to_slice y.to_slice := by
    simp [core.array.equality.PartialEqArray.eq,core.slice.cmp.PartialEqSlice.eq]
  rw [eq]
  step with core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU32 x.to_slice y.to_slice
    (by intro a b; simp [core.cmp.PartialEqU32,step_simps]) as ⟨b,h⟩
  have equiv : x.to_slice=y.to_slice ↔ x=y := by
    constructor
    · intro e; apply Aeneas.Std.Array.ext; simpa only [Array.val_to_slice] using congrArg Slice.val e
    · rintro rfl; rfl
  simp [step_simps,h,equiv]

def remaining {width : Usize} (ix stop : Array U32 width) : Nat :=
  ∑ j : Fin width.val, (stop.val[j.val]!.val - ix.val[j.val]!.val)

theorem remaining_decreases {width : Usize} (ix next stop : Array U32 width)
    (different : ix≠stop)
    (bounds : ∀ j < width.val, ix.val[j]!.val ≤ stop.val[j]!.val)
    (advance : ∀ j < width.val, next.val[j]!.val = ix.val[j]!.val+
      (if ix.val[j]!.val < stop.val[j]!.val then 1 else 0)) :
    remaining next stop < remaining ix stop := by
  have live : ∃ j : Fin width.val, ix.val[j.val]!.val < stop.val[j.val]!.val := by
    by_contra! h
    apply different
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have small : i < width.val := by simpa using hi
      have same := Nat.le_antisymm (bounds i small) (h ⟨i,small⟩)
      apply UScalar.eq_of_val_eq
      rw [← getElem!_pos,← getElem!_pos]
      exact same
  unfold remaining
  apply Finset.sum_lt_sum
  · intro j _
    have := advance j.val j.isLt
    split_ifs at this <;> omega
  · obtain ⟨j,h⟩ := live
    refine ⟨j,Finset.mem_univ _,?_⟩
    have := advance j.val j.isLt
    rw [if_pos h] at this
    omega

end slhdsa.ShakeBatch
