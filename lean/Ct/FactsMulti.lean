import Ct.Facts

/-! Inversion facts for the primitives of this translation that the single-set tree's
`Ct/Facts.lean` does not cover: mutable sub-slices of slices (`&mut s[a..b]`). Used by
`ct_facts` (`Ct/Tactic.lean`). -/

open Aeneas Aeneas.Std

namespace Ct.Facts

theorem slice_range_index_mut_len {α : Type u} {s : Slice α} {r : core.ops.range.Range Usize}
    {a : Slice α} {back : Slice α → Slice α}
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) s r =
      Result.ok (a, back)) :
    a.length = r.end.val - r.start.val ∧ r.end.val ≤ s.length := by
  simp only [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut] at h
  split at h
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rename_i hc
    simp only [UScalar.le_equiv] at hc
    simp [Slice.length, List.slice_length] at hc ⊢
    omega
  · simp at h

theorem slice_range_index_mut_back {α : Type u} {s : Slice α} {r : core.ops.range.Range Usize}
    {a : Slice α} {back : Slice α → Slice α}
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) s r =
      Result.ok (a, back)) :
    ∀ y, (back y).length = s.length := by
  simp only [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut] at h
  split at h
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro y
    simp [Slice.length]
  · simp at h

end Ct.Facts
