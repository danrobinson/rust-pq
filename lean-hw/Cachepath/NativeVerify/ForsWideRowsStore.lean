import Cachepath.NativeVerify.ForsWideRowsProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsWideRows
open ShakeBatch

def Filled {N : Usize} (target : Nat → Spec.Bytes) (len pos : Nat) (out : Slice (Array U8 N)) :=
  out.length=len ∧ ∀ j < pos, bytes out.val[j]!.val=target j

def writeRows {N : Usize} (out : Slice (Array U8 N)) (i stop active : Usize) (src : Array (Array U8 N) 8#usize) := do
  let (part,back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N)) out {start:=i,«end»:=stop}
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) src {«end»:=active}
  let copied ← core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N core.marker.CopyU8) part s
  ok (back copied)

theorem writeBind {α} {N : Usize} (out : Slice (Array U8 N)) (i stop active : Usize)
    (src : Array (Array U8 N) 8#usize) (f : Slice (Array U8 N) → Result α) :
    (writeRows out i stop active src >>= f) = (do
      let (part,back) ← core.slice.index.SliceIndexRangeUsizeSlice.index_mut {start:=i,«end»:=stop} out
      let s ← core.slice.index.SliceIndexRangeToUsizeSlice.index {«end»:=active} src.to_slice
      let copied ← core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N core.marker.CopyU8) part s
      f (back copied)) := by
  simp only [writeRows,bind_tc_eq,Std.bind_assoc,bind_ok]
  rfl

theorem write_rows {N : Usize} (out : Slice (Array U8 N)) (i stop active : Usize)
    (src : Array (Array U8 N) 8#usize) (target : Nat → Spec.Bytes) (len : Nat)
    (old : Filled target len i.val out) (stopAt : stop.val=i.val+active.val) (fit : stop.val ≤ len)
    (live : active.val ≤ 8) (computed : ∀ j < active.val, bytes src.val[j]!.val=target (i.val+j)) :
    writeRows out i stop active src ⦃ after => Filled target len stop.val after ⦄ := by
  obtain ⟨length,prior⟩ := old
  unfold writeRows
  step as ⟨pair,_,plen,save⟩
  obtain ⟨part,back⟩ := pair
  dsimp only at plen save ⊢
  step as ⟨s,take,taken⟩
  step as ⟨copied,cp⟩
  all_goals try omega
  constructor
  · change ((back copied).val).length=len
    rw [save,Slice.setSlice!_val,List.length_setSlice!];exact length
  · intro j hj
    rw [save,cp,Slice.setSlice!_val]
    by_cases earlier : j < i.val
    · rw [List.getElem!_setSlice!_prefix _ _ _ _ earlier];exact prior j earlier
    · rw [List.getElem!_setSlice!_middle _ _ _ _ (by change _ ∧ j-i.val < s.length ∧ j < out.length;omega),
        take,List.getElem!_slice _ _ _ _ (by simp;omega),Nat.zero_add,Array.val_to_slice,
        computed _ (by omega),Nat.add_sub_of_le (by omega)]

theorem min_count (left : Usize) :
    (core.cmp.impls.OrdUsize.min left 8#usize).val=min left.val 8 := by
  change (if 8#usize < left then 8#usize else left).val=_
  split <;> rename_i h
  · exact (min_eq_right (Nat.le_of_lt h)).symm
  · exact (min_eq_left (Nat.le_of_not_gt h)).symm

end slhdsa.NativeVerify.ForsWideRows
