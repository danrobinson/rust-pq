import Ct.Leak

/-! Inversion facts about successful Aeneas primitives (lengths of their results), used to
carry "equal length" through the relational proofs. -/

open Aeneas Aeneas.Std

namespace Ct.Facts

theorem push_ok {α : Type u} {v : alloc.vec.Vec α} {x : α} {a : alloc.vec.Vec α}
    (h : alloc.vec.Vec.push v x = Result.ok a) : a.length = v.length + 1 := by
  simp only [alloc.vec.Vec.push] at h
  split at h
  · simp only [Result.ok.injEq] at h; subst h; simp [alloc.vec.Vec.length]
  · simp at h

theorem extend_ok {α : Type u} {c : core.clone.Clone α} {v : alloc.vec.Vec α} {s : Slice α}
    {a : alloc.vec.Vec α}
    (h : alloc.vec.Vec.extend_from_slice c v s = Result.ok a) : a.length = v.length + s.length := by
  simp only [alloc.vec.Vec.extend_from_slice] at h
  split at h
  · rw [Aeneas.Std.bind_tc_eq, bind_eq_ok] at h
    obtain ⟨l, -, hl⟩ := h
    simp only [Result.ok.injEq] at hl; subst hl
    simp [alloc.vec.Vec.length, l.property]
  · simp at h

theorem copy_ok {α : Type u} {c : core.marker.Copy α} {s src a : Slice α}
    (h : core.slice.Slice.copy_from_slice c s src = Result.ok a) :
    a = src ∧ s.length = src.length := by
  simp only [core.slice.Slice.copy_from_slice] at h
  split at h
  · simp only [Result.ok.injEq] at h
    rename_i hl
    refine ⟨h.symm, ?_⟩
    have := congrArg UScalar.val hl
    simpa [Slice.len_val] using this
  · simp at h

theorem range_ok {α : Type u} {s a : Slice α} {r : core.ops.range.Range Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice α) s r =
      Result.ok a) :
    a.length = r.end.val - r.start.val ∧ r.end.val ≤ s.length := by
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · simp only [Result.ok.injEq] at h; subst h
    rename_i hc
    simp only [UScalar.le_equiv] at hc
    simp [Slice.length, List.slice_length] at hc ⊢
    omega
  · simp at h

theorem slice_index_mut_ok {α : Type u} {s : Slice α} {i : Usize} {x : α} {back : α → Slice α}
    (h : Slice.index_mut_usize s i = Result.ok (x, back)) : ∀ y, (back y).length = s.length := by
  simp only [Slice.index_mut_usize, Aeneas.Std.bind_tc_eq, bind_eq_ok] at h
  obtain ⟨_, -, h⟩ := h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  intro y; exact Slice.set_length s i y

theorem array_range_index_mut_ok {α : Type u} {N : Usize} {a : Array α N}
    {r : core.ops.range.Range Usize} {s : Slice α} {back : Slice α → Array α N}
    (h : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice α)) a r =
        Result.ok (s, back)) :
    s.length = r.end.val - r.start.val := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Aeneas.Std.bind_tc_eq] at h
  split at h
  · rw [bind_ok] at h
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rename_i hc
    simp only [UScalar.le_equiv] at hc
    simp [Slice.length, List.slice_length, Array.to_slice] at hc ⊢
    omega
  · simp at h

theorem array_range_index_ok {α : Type u} {N : Usize} {a : Array α N}
    {r : core.ops.range.Range Usize} {s : Slice α}
    (h : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice α)) a r =
        Result.ok s) :
    s.length = r.end.val - r.start.val := by
  simp only [core.array.Array.index, core.ops.index.IndexSlice] at h
  exact (range_ok h).1

theorem slice_len_congr {α : Type u} {β : Type v} {s : Slice α} {s' : Slice β}
    (h : s.length = s'.length) : s.len = s'.len := by
  apply UScalar.eq_of_val_eq; simp [h]

theorem vec_len_congr {α : Type u} {β : Type v} {s : alloc.vec.Vec α} {s' : alloc.vec.Vec β}
    (h : s.length = s'.length) : s.len = s'.len := by
  apply UScalar.eq_of_val_eq; simp [h]

@[simp] theorem deref_length {α : Type u} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).length = v.length := by
  simp [alloc.vec.Vec.deref, alloc.vec.Vec.length, Slice.length, alloc.vec.Vec.val]

end Ct.Facts
