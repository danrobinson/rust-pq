import Parallel.ForsMergeProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsMetadata
def target_wide (a : Std.U32) : Result Std.U32 := do
  if a >= 10#u32
  then ok 9#u32
  else if a >= 9#u32
       then ok 8#u32
       else ok a

def meta_wide
  (fors_indices : alloc.vec.Vec Std.U32) (a : Std.U32) (j : Std.U32)
  (fors_target : Std.U32) (fors_split_count : Std.Usize) (t : Std.U32)
  (fors_split_meta : alloc.vec.Vec ParallelForsMerge.Meta) :
  Result (Std.Usize × (alloc.vec.Vec ParallelForsMerge.Meta))
  := do
  let i ← lift (UScalar.cast .Usize t)
  let idx ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
      fors_indices i
  let i1 ← a - j
  let i2 ← t <<< i1
  let i3 ← idx >>> j
  let i4 ← lift (i3 ^^^ 1#u32)
  let root_idx ← i2 + i4
  let split ← lift (core.num.U32.saturating_sub j fors_target)
  let chunks ← 1#usize <<< split
  let fors_split_count1 ← fors_split_count + chunks
  let fors_split_meta1 ←
    alloc.vec.Vec.push fors_split_meta
      ({
         tree := t,
         height := j,
         root_idx,
         sub_h := fors_target,
         slot_start := fors_split_count,
         chunks
       } : ParallelForsMerge.Meta)
  ok (fors_split_count1, fors_split_meta1)

def target_group (a : Std.U32) : Result Std.U32 := do
  if a >= 10#u32
  then ok 9#u32
  else if a >= 9#u32
       then ok 8#u32
       else ok a

@[rust_loop_body]
def meta_group_loop.body
  (fors_indices : alloc.vec.Vec Std.U32) (a : Std.U32) (j : Std.U32)
  (fors_target : Std.U32) (first : Std.Usize) (chunks : Std.Usize)
  (split_base : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (fors_split_meta : alloc.vec.Vec ParallelForsMerge.Meta) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    ParallelForsMerge.Meta)) (alloc.vec.Vec
    ParallelForsMerge.Meta))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done fors_split_meta)
  | some lane =>
    let i ← first + lane
    let t ← lift (UScalar.cast .U32 i)
    let i1 ← a - j
    let i2 ← t <<< i1
    let i3 ← lift (UScalar.cast .Usize t)
    let i4 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
        fors_indices i3
    let i5 ← i4 >>> j
    let i6 ← lift (i5 ^^^ 1#u32)
    let root_idx ← i2 + i6
    let i7 ← lane * chunks
    let i8 ← split_base + i7
    let fors_split_meta1 ←
      alloc.vec.Vec.push fors_split_meta
        ({
           tree := t,
           height := j,
           root_idx,
           sub_h := fors_target,
           slot_start := i8,
           chunks
         } : ParallelForsMerge.Meta)
    ok (cont (iter1, fors_split_meta1))

@[rust_loop]
def meta_group_loop
  (iter : core.ops.range.Range Std.Usize)
  (fors_indices : alloc.vec.Vec Std.U32) (a : Std.U32) (j : Std.U32)
  (fors_target : Std.U32) (first : Std.Usize)
  (fors_split_meta : alloc.vec.Vec ParallelForsMerge.Meta)
  (chunks : Std.Usize) (split_base : Std.Usize) :
  Result (alloc.vec.Vec ParallelForsMerge.Meta)
  := do
  loop
    (fun (iter1, fors_split_meta1) => meta_group_loop.body
      fors_indices a j fors_target first chunks split_base iter1
      fors_split_meta1)
    (iter, fors_split_meta)

def meta_group
  (fors_indices : alloc.vec.Vec Std.U32) (a : Std.U32) (j : Std.U32)
  (fors_target : Std.U32) (fors_split_count : Std.Usize) (first : Std.Usize)
  (active : Std.Usize)
  (fors_split_meta : alloc.vec.Vec ParallelForsMerge.Meta) :
  Result (Std.Usize × (alloc.vec.Vec ParallelForsMerge.Meta))
  := do
  let split ← j - fors_target
  let chunks ← 1#usize <<< split
  let i ← active * chunks
  let fors_split_count1 ← fors_split_count + i
  let fors_split_meta1 ←
    meta_group_loop { start := 0#usize, «end» := active }
      fors_indices a j fors_target first fors_split_meta chunks
      fors_split_count
  ok (fors_split_count1, fors_split_meta1)

def target_scalar (a : Std.U32) : Result Std.U32 := do
  if a >= 10#u32
  then ok 9#u32
  else ok a

def meta_scalar
  (fors_indices : alloc.vec.Vec Std.U32) (a : Std.U32) (j : Std.U32)
  (fors_target : Std.U32) (fors_split_count : Std.Usize) (t : Std.U32)
  (fors_split_meta : alloc.vec.Vec ParallelForsMerge.Meta) :
  Result (Std.Usize × (alloc.vec.Vec ParallelForsMerge.Meta))
  := do
  let i ← lift (UScalar.cast .Usize t)
  let idx ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
      fors_indices i
  let i1 ← a - j
  let i2 ← t <<< i1
  let i3 ← idx >>> j
  let i4 ← lift (i3 ^^^ 1#u32)
  let root_idx ← i2 + i4
  let split ← j - fors_target
  let chunks ← 1#usize <<< split
  let fors_split_count1 ← fors_split_count + chunks
  let fors_split_meta1 ←
    alloc.vec.Vec.push fors_split_meta
      ({
         tree := t,
         height := j,
         root_idx,
         sub_h := fors_target,
         slot_start := fors_split_count,
         chunks
       } : ParallelForsMerge.Meta)
  ok (fors_split_count1, fors_split_meta1)
end slhdsa.ForsMetadata
