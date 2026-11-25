import Parallel.ReduceNative
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelForsMerge
structure Meta where
  tree : Std.U32
  height : Std.U32
  root_idx : Std.U32
  sub_h : Std.U32
  slot_start : Std.Usize
  chunks : Std.Usize

def merge_fors
  {N : Std.Usize} («meta» : Meta)
  (fors_split : alloc.vec.Vec (Option (Array Std.U8 N)))
  (seed : Array Std.U8 N) (fors_addr : address.Adrs) (fors_stride : Std.Usize)
  :
  Result (Std.Usize × (Array Std.U8 N))
  := do
  let i ← «meta».slot_start + «meta».chunks
  let s ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice
      (Option (Array Std.U8 N))) fors_split
      { start := «meta».slot_start, «end» := i }
  let val ←
    @ParallelReduceNative.reduce_tree ParallelReduceNative.shakeFamily N s seed fors_addr «meta».root_idx
      «meta».sub_h «meta».height
  let i1 ← lift (UScalar.cast .Usize «meta».tree)
  let i2 ← i1 * fors_stride
  let i3 ← i2 + 1#usize
  let i4 ← lift (UScalar.cast .Usize «meta».height)
  let i5 ← i3 + i4
  ok (i5, val)
end slhdsa.ParallelForsMerge
