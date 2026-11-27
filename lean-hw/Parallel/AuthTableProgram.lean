import Parallel.ReduceNative
import Parallel.SignJoinProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelAuthTable
noncomputable section
structure XmssAuthMeta where
  slot_start : Std.Usize
  split : Std.U32
  root_idx : Std.U32
  height : Std.U32


def read_node {N : Usize} (xmss_slots : alloc.vec.Vec (Option (Array U8 N))) (seed : Array U8 N)
    (tree_addr : address.Adrs) («meta» : XmssAuthMeta) : Result (Array U8 N) :=
  if «meta».split = 0#u32
      then
        do
        let ol ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            (Option (Array Std.U8 N))) xmss_slots
            «meta».slot_start
        let o1 ← ParallelSignJoin.readCell ol
        core.option.Option.expect o1 (toStr "XMSS auth slot filled")
      else
        do
        let count ← 1#usize <<< «meta».split
        let i2 ← «meta».slot_start + count
        let s ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice
            (Option (Array Std.U8 N))) xmss_slots
            { start := «meta».slot_start, «end» := i2 }
        let i3 ← «meta».height - «meta».split
        @ParallelReduceNative.reduce_tree ParallelReduceNative.shakeFamily N s seed tree_addr «meta».root_idx i3
          «meta».height

@[rust_loop_body]
def auth_table_loop0_loop0.body
  {N : Std.Usize} (hp : Std.Usize)
  (xmss_meta : alloc.vec.Vec XmssAuthMeta)
  (xmss_slots : alloc.vec.Vec (Option (Array Std.U8 N)))
  (seed : Array Std.U8 N) (j : Std.Usize) (tree_addr : address.Adrs)
  (iter : core.ops.range.Range Std.Usize)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done xmss_auth)
  | some h =>
    let i ← j * hp
    let i1 ← i + h
    let «meta» ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        XmssAuthMeta) xmss_meta i1
    let node ← read_node xmss_slots seed tree_addr «meta»
    let xmss_auth1 ← alloc.vec.Vec.push xmss_auth node
    ok (cont (iter1, xmss_auth1))

@[rust_loop]
def auth_table_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (hp : Std.Usize)
  (xmss_meta : alloc.vec.Vec XmssAuthMeta)
  (xmss_slots : alloc.vec.Vec (Option (Array Std.U8 N)))
  (seed : Array Std.U8 N) (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (j : Std.Usize) (tree_addr : address.Adrs) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, xmss_auth1) => auth_table_loop0_loop0.body
      hp xmss_meta xmss_slots seed j tree_addr iter1 xmss_auth1)
    (iter, xmss_auth)

@[rust_loop_body]
def auth_table_loop0.body
  {N : Std.Usize} (hp : Std.Usize)
  (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (xmss_meta : alloc.vec.Vec XmssAuthMeta)
  (xmss_slots : alloc.vec.Vec (Option (Array Std.U8 N)))
  (seed : Array Std.U8 N) (iter : core.ops.range.Range Std.Usize)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done xmss_auth)
  | some j =>
    let (addr, _) ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (address.Adrs
        × Std.U32)) layers j
    let tree_addr ← address.Adrs.with_type addr address.TREE
    let xmss_auth1 ←
      auth_table_loop0_loop0
        { start := 0#usize, «end» := hp } hp xmss_meta xmss_slots seed
        xmss_auth j tree_addr
    ok (cont (iter1, xmss_auth1))

@[rust_loop]
def auth_table_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (hp : Std.Usize)
  (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (xmss_meta : alloc.vec.Vec XmssAuthMeta)
  (xmss_slots : alloc.vec.Vec (Option (Array Std.U8 N)))
  (seed : Array Std.U8 N) (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, xmss_auth1) => auth_table_loop0.body hp
      layers xmss_meta xmss_slots seed iter1 xmss_auth1)
    (iter, xmss_auth)

def auth_table
  {N : Std.Usize} (d : Std.Usize) (hp : Std.Usize)
  (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (xmss_meta : alloc.vec.Vec XmssAuthMeta)
  (xmss_slots : alloc.vec.Vec (Option (Array Std.U8 N)))
  (seed : Array Std.U8 N) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let i ← d * hp
  let xmss_auth := alloc.vec.Vec.with_capacity (Array Std.U8 N) i
  auth_table_loop0 { start := 0#usize, «end» := d } hp
    layers xmss_meta xmss_slots seed xmss_auth
end
end slhdsa.ParallelAuthTable
