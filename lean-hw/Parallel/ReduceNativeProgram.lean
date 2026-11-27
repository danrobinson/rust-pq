import Slhdsa.Proofs.ShakeXmss
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelReduceNative
noncomputable section
class Family where
  Seed : Usize → Type
  hash {N : Usize} : Seed N → address.Adrs → Array U8 N → Array U8 N → Result (Array U8 N)
variable [family : Family]

def getCell {α : Type} (cell : Option α) : Result (Option α) := ok cell

def truncate {α : Type} (v : alloc.vec.Vec α) (n : Usize) : Result (alloc.vec.Vec α) :=
  ok (alloc.vec.Vec.from (v.val.take n.val) ((List.length_take_le ..).trans (by scalar_tac)))

@[reducible]
def reduce_tree.closure (N : Std.Usize) := Unit

def
  reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut
  {N : Std.Usize} (c : reduce_tree.closure N)
  (tupled_args : Option (Array Std.U8 N)) :
  Result ((Array Std.U8 N) × (reduce_tree.closure N))
  := do
  let o ← getCell tupled_args
  let a ← core.option.Option.expect o (toStr "subtree job completed")
  ok (a, ())

def
  reduce_tree.closure.Insts.CoreOpsFunctionFnOnceTupleShared0OnceLockArrayU8NArrayU8N.call_once
  {N : Std.Usize} (c : reduce_tree.closure N)
  (ol : Option (Array Std.U8 N)) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut
      () ol
  ok a

@[reducible]
def
  reduce_tree.closure.Insts.CoreOpsFunctionFnOnceTupleShared0OnceLockArrayU8NArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (reduce_tree.closure N) (Option
  (Array Std.U8 N)) (Array Std.U8 N) := {
  call_once :=
    reduce_tree.closure.Insts.CoreOpsFunctionFnOnceTupleShared0OnceLockArrayU8NArrayU8N.call_once
}

@[reducible]
def
  reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut
  (reduce_tree.closure N) (Option
  (Array Std.U8 N)) (Array Std.U8 N) := {
  FnOnceInst :=
    reduce_tree.closure.Insts.CoreOpsFunctionFnOnceTupleShared0OnceLockArrayU8NArrayU8N
    N
  call_mut :=
    reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut
}


/-- Read-only slots retain slice order. Iterator allocation and Rust's OnceLock memory
ordering are modeled at this boundary. Each element still runs the extracted expect closure. -/
def collectRows {N : Usize} (slots : Slice (Option (Array U8 N))) : Result (alloc.vec.Vec (Array U8 N)) := do
  let xs ← slots.val.mapM (fun slot => do
    let (v,_) ← reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut (N:=N) () slot
    ok v)
  if h : xs.length ≤ Usize.max then ok (alloc.vec.Vec.from xs h) else fail .panic

@[rust_loop_body]
def reduce_tree_loop0_loop0.body
  {N : Std.Usize} (seed : family.Seed N) (adrs : address.Adrs) (lvl : Std.U32)
  (base : Std.U32) (iter : core.ops.range.Range Std.Usize)
  (cur : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done cur)
  | some idx =>
    let a ← address.Adrs.with_word2 adrs lvl
    let i ← lift (UScalar.cast .U32 idx)
    let i1 ← base + i
    let a1 ← address.Adrs.with_word3 a i1
    let i2 ← 2#usize * idx
    let a2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) cur i2
    let i3 ← i2 + 1#usize
    let a3 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) cur i3
    let a4 ← family.hash seed a1 a2 a3
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
        Std.U8 N)) cur idx
    let cur1 := index_mut_back a4
    ok (cont (iter1, cur1))

@[rust_loop]
def reduce_tree_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : family.Seed N) (adrs : address.Adrs)
  (cur : alloc.vec.Vec (Array Std.U8 N)) (lvl : Std.U32) (base : Std.U32) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, cur1) => reduce_tree_loop0_loop0.body seed
      adrs lvl base iter1 cur1)
    (iter, cur)

@[rust_loop_body]
def reduce_tree_loop0.body
  {N : Std.Usize} (seed : family.Seed N) (adrs : address.Adrs)
  (root_idx : Std.U32) (height : Std.U32)
  (iter : core.ops.range.RangeInclusive Std.U32)
  (cur : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.U32) ×
    (alloc.vec.Vec (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepU32 iter
  match o with
  | none => ok (done cur)
  | some lvl =>
    let shift ← height - lvl
    let base ← root_idx <<< shift
    let i := alloc.vec.Vec.len cur
    let next_len ← i / 2#usize
    let cur1 ←
      reduce_tree_loop0_loop0
        { start := 0#usize, «end» := next_len } seed adrs cur lvl base
    let cur2 ← truncate cur1 next_len
    ok (cont (iter1, cur2))

@[rust_loop]
def reduce_tree_loop0
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.U32)
  (seed : family.Seed N) (adrs : address.Adrs) (root_idx : Std.U32)
  (height : Std.U32) (cur : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, cur1) => reduce_tree_loop0.body seed adrs
      root_idx height iter1 cur1)
    (iter, cur)

def reduce_tree
  {N : Std.Usize}
  (slots : Slice (Option (Array Std.U8 N)))
  (seed : family.Seed N) (adrs : address.Adrs) (root_idx : Std.U32)
  (sub_h : Std.U32) (height : Std.U32) :
  Result (Array Std.U8 N)
  := do
  let cur ← collectRows slots
  let i1 ← sub_h + 1#u32
  let iter ← core.ops.range.RangeInclusive.new i1 height
  let cur1 ←
    reduce_tree_loop0 iter seed adrs root_idx height cur
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8 N))
    cur1 0#usize
end
end slhdsa.ParallelReduceNative
