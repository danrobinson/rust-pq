import Buffered.Gather
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered
open ShakeBatch

abbrev Stack (N : Usize) := Array (Row16 N) 17#usize

/-- The full physical matrix frame, including cells past the occupied prefix. -/
def Stored {N depth : Usize} (before after : Array (Row16 N) depth) (level pos count : Nat) (src : Rows8 N) : Prop :=
  ∀ h j, after.val[h]!.val[j]! =
    if h = level ∧ pos ≤ j ∧ j < pos+count then src.val[j-pos]! else before.val[h]!.val[j]!

theorem stored_cells_at {N depth : Usize} (before : Array (Row16 N) depth) (level : Usize) (pos count : Nat)
    (src : Rows8 N) (row : Row16 N) (inside : level.val < depth.val) (fit : pos+count ≤ 16)
    (live : count ≤ 8)
    (write : row.val = before.val[level.val]!.val.setSlice! pos (src.val.take count)) :
    Stored before (before.set level row) level.val pos count src := by
  intro h j
  rw [Array.set_val_eq]
  by_cases same : h = level.val
  · subst h
    rw [setSame _ _ _ (by simpa using inside),write]
    have size : (src.val.take count).length=count := by simp [live]
    by_cases hit : pos ≤ j ∧ j < pos+count
    · rw [if_pos ⟨rfl,hit⟩,List.getElem!_setSlice!_middle _ _ _ _ (by simp [size];omega)]
      exact List.getElem!_take_of_lt _ _ _ (by omega)
    · rw [if_neg (by simp [hit])]
      by_cases early : j<pos
      · exact List.getElem!_setSlice!_prefix _ _ _ _ early
      · exact List.getElem!_setSlice!_suffix _ _ _ _ (by rw [size];omega)
  · rw [setOther _ _ _ _ (Ne.symm same),if_neg (by simp [same])]

theorem stored_cells {N : Usize} (before : Stack N) (level : Usize) (pos count : Nat)
    (src : Rows8 N) (row : Row16 N) (inside : level.val < 17) (fit : pos+count ≤ 16)
    (live : count ≤ 8)
    (write : row.val = before.val[level.val]!.val.setSlice! pos (src.val.take count)) :
    Stored before (before.set level row) level.val pos count src :=
  stored_cells_at before level pos count src row inside fit live write

def storeFull {N : Usize} (before : Stack N) (level pos : Usize) (src : Rows8 N) : Result (Stack N) := do
  let (row, restore) ← Array.index_mut_usize before level
  let stop ← pos+8#usize
  let (dst, put) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N))) row {start:=pos,«end»:=stop}
  let s ← lift (Array.to_slice src)
  let out ← core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N core.marker.CopyU8) dst s
  ok (restore (put out))

def storePrefix {N : Usize} (before : Stack N) (level pos count : Usize) (src : Rows8 N) : Result (Stack N) := do
  let (row, restore) ← Array.index_mut_usize before level
  let stop ← pos+count
  let (dst, put) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N))) row {start:=pos,«end»:=stop}
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) src {«end»:=count}
  let out ← core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N core.marker.CopyU8) dst s
  ok (restore (put out))

theorem full_store {N : Usize} (before : Stack N) (level pos : Usize) (src : Rows8 N)
    (inside : level.val < 17) (fit : pos.val+8 ≤ 16) :
    storeFull before level pos src ⦃ after => Stored before after level.val pos.val 8 src ⦄ := by
  unfold storeFull
  step as ⟨row,restore,get,save⟩
  step as ⟨stop,sv⟩
  step as ⟨dst,put,rv,rl,write⟩
  simp only [lift,bind_ok]
  step as ⟨out,copy⟩
  rw [save]
  apply stored_cells _ _ _ _ _ _ inside fit (by decide)
  rw [write,copy,Array.val_to_slice,get,←getElem!_pos,List.take_of_length_le (by simp)]

theorem prefix_store {N : Usize} (before : Stack N) (level pos count : Usize) (src : Rows8 N)
    (inside : level.val < 17) (fit : pos.val+count.val ≤ 16) (live : count.val ≤ 8) :
    storePrefix before level pos count src ⦃ after => Stored before after level.val pos.val count.val src ⦄ := by
  unfold storePrefix
  step as ⟨row,restore,get,save⟩
  step as ⟨stop,sv⟩
  step as ⟨dst,put,rv,rl,write⟩
  step as ⟨s,take,taken⟩
  step as ⟨out,copy⟩
  · omega
  rw [save]
  apply stored_cells _ _ _ _ _ _ inside fit live
  rw [write,copy,take,get,←getElem!_pos]
  simp [List.slice,Array.val_to_slice]

end slhdsa.Buffered
