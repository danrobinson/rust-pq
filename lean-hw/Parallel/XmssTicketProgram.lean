import Shakebatch.WidthThreeNative
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelXmssTicket
abbrev Node (N : Usize) := Array U8 N → U32 → U32 → Array U8 N → address.Adrs → Result (Array U8 N)

def subtree_ticket
  {N : Std.Usize} (node : Node N) (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (layer : Std.U16) (idx : Std.U32) (height : Std.U32) (slot : Std.Usize)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) :
  Result (Std.Usize × (Array Std.U8 N))
  := do
  let i ← lift (UScalar.cast .Usize layer)
  let (addr, _) ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (address.Adrs ×
      Std.U32)) layers i
  let val ← node sk idx height seed addr
  ok (slot, val)


def leaf_ticket
  {N : Std.Usize} (node : Node N) (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (layer : Std.U16) (sk : Array Std.U8 N) (seed : Array Std.U8 N) :
  Result (Std.Usize × (Array Std.U8 N))
  := do
  let i ← lift (UScalar.cast .Usize layer)
  let (addr, index) ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (address.Adrs ×
      Std.U32)) layers i
  let val ← node sk index 0#u32 seed addr
  let i1 ← lift (UScalar.cast .Usize layer)
  ok (i1, val)


@[rust_loop_body]
def build_layers_loop.body
  (i : Std.U32) (iter : core.ops.range.Range Std.U32) (tree : Std.U64)
  (leaf : Std.U32) (layers : alloc.vec.Vec (address.Adrs × Std.U32)) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × Std.U64 × Std.U32 ×
    (alloc.vec.Vec (address.Adrs × Std.U32))) (alloc.vec.Vec (address.Adrs ×
    Std.U32)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done layers)
  | some j =>
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_layer a j
    let a2 ← address.Adrs.with_tree a1 tree
    let layers1 ← alloc.vec.Vec.push layers (a2, leaf)
    let i1 ← 1#u64 <<< i
    let i2 ← i1 - 1#u64
    let i3 ← lift (tree &&& i2)
    let leaf1 ← lift (UScalar.cast .U32 i3)
    let tree1 ← tree >>> i
    ok (cont (iter1, tree1, leaf1, layers1))


@[rust_loop]
def build_layers_loop
  (iter : core.ops.range.Range Std.U32) (i : Std.U32) (tree : Std.U64)
  (leaf : Std.U32) (layers : alloc.vec.Vec (address.Adrs × Std.U32)) :
  Result (alloc.vec.Vec (address.Adrs × Std.U32))
  := do
  loop
    (fun (iter1, tree1, leaf1, layers1) =>
      build_layers_loop.body i iter1 tree1 leaf1 layers1)
    (iter, tree, leaf, layers)


def build_layers
  (p : params.Params) (tree : Std.U64) (leaf : Std.U32) :
  Result (alloc.vec.Vec (address.Adrs × Std.U32))
  := do
  let d ← lift (UScalar.cast .Usize p.d)
  let layers := alloc.vec.Vec.with_capacity (address.Adrs × Std.U32) d
  build_layers_loop { start := 0#u32, «end» := p.d } 
    p.hp tree leaf layers
end slhdsa.ParallelXmssTicket
