import Slhdsa.Proofs.ShakeXmss
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelRootWalk
abbrev Hash (N : Usize) := Array U8 N → address.Adrs → Array U8 N → Array U8 N → Result (Array U8 N)
@[rust_loop_body]
def root_walk_loop.body
  {N : Std.Usize} (hash : Hash N) (j : Std.Usize) (hp : Std.Usize) (tree_addr : address.Adrs)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) (seed : Array Std.U8 N)
  (iter : core.ops.range.Range Std.U32) (node : Array Std.U8 N)
  (index : Std.U32) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array Std.U8 N) ×
    Std.U32) (Array Std.U8 N))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done node)
  | some h =>
    let i ← j * hp
    let i1 ← lift (UScalar.cast .Usize h)
    let i2 ← i + i1
    let sibling ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) xmss_auth i2
    let parent ← index >>> 1#i32
    let i3 ← h + 1#u32
    let a ← address.Adrs.with_word2 tree_addr i3
    let a_node ← address.Adrs.with_word3 a parent
    let i4 ← lift (index &&& 1#u32)
    if i4 = 0#u32
    then
      let node1 ← hash seed a_node node sibling
      ok (cont (iter1, node1, parent))
    else
      let node1 ← hash seed a_node sibling node
      ok (cont (iter1, node1, parent))

@[rust_loop]
def root_walk_loop
  {N : Std.Usize} (hash : Hash N) (iter : core.ops.range.Range Std.U32) (j : Std.Usize)
  (hp : Std.Usize) (tree_addr : address.Adrs) (node : Array Std.U8 N)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) (seed : Array Std.U8 N)
  (index : Std.U32) :
  Result (Array Std.U8 N)
  := do
  loop
    (fun (iter1, node1, index1) => root_walk_loop.body hash j hp
      tree_addr xmss_auth seed iter1 node1 index1)
    (iter, node, index)

@[reducible]
def root_walk
  {N : Std.Usize} (hash : Hash N) (p : params.Params) (j : Std.Usize) (hp : Std.Usize)
  (tree_addr : address.Adrs) (leaf_idx : Std.U32) (node : Array Std.U8 N)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) (seed : Array Std.U8 N) :
  Result (Array Std.U8 N)
  := do
  root_walk_loop hash { start := 0#u32, «end» := p.hp } j hp
    tree_addr node xmss_auth seed leaf_idx
end slhdsa.ParallelRootWalk
