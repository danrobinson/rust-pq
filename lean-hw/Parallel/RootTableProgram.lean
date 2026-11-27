import Parallel.RootWalk
import Parallel.SignJoinProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelRootWalk
class Engine where
  hash {N : Usize} : Hash N
  recover {N : Usize} : params.Params → Slice U8 → Slice U8 → Array U8 N → address.Adrs → Result (Array U8 N)
set_option linter.concreteInstances false
variable [engine : Engine]
@[rust_loop_body]
def all_roots_loop0_loop0.body
  {N : Std.Usize} (hp : Std.Usize) (seed : Array Std.U8 N)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) (j : Std.Usize)
  (tree_addr : address.Adrs) (iter : core.ops.range.Range Std.U32)
  (node : Array Std.U8 N) (index : Std.U32) :
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
      let node1 ← engine.hash seed a_node node sibling
      ok (cont (iter1, node1, parent))
    else
      let node1 ← engine.hash seed a_node sibling node
      ok (cont (iter1, node1, parent))

@[rust_loop]
def all_roots_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (hp : Std.Usize)
  (seed : Array Std.U8 N) (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (j : Std.Usize) (tree_addr : address.Adrs) (node : Array Std.U8 N)
  (index : Std.U32) :
  Result (Array Std.U8 N)
  := do
  loop
    (fun (iter1, node1, index1) =>
      all_roots_loop0_loop0.body hp seed xmss_auth j
      tree_addr iter1 node1 index1)
    (iter, node, index)

@[rust_loop_body]
def all_roots_loop0.body
  {N : Std.Usize} (p : params.Params) (hp : Std.Usize) (seed : Array Std.U8 N)
  (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (leaf_pks : alloc.vec.Vec (Option (Array Std.U8 N)))
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (iter : core.ops.range.Range Std.Usize)
  (roots : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done roots)
  | some j =>
    let (addr, leaf_idx) ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (address.Adrs
        × Std.U32)) layers j
    let tree_addr ← address.Adrs.with_type addr address.TREE
    let ol ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (Option (Array Std.U8 N))) leaf_pks j
    let o1 ← ParallelSignJoin.readCell ol
    let node ← core.option.Option.expect o1 (toStr "leaf PK filled")
    let node1 ←
      all_roots_loop0_loop0
        { start := 0#u32, «end» := p.hp } hp seed xmss_auth j tree_addr node
        leaf_idx
    let roots1 ← alloc.vec.Vec.push roots node1
    ok (cont (iter1, roots1))

@[rust_loop]
def all_roots_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (p : params.Params)
  (hp : Std.Usize) (seed : Array Std.U8 N)
  (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (leaf_pks : alloc.vec.Vec (Option (Array Std.U8 N)))
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (roots : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, roots1) => all_roots_loop0.body p hp seed
      layers leaf_pks xmss_auth iter1 roots1)
    (iter, roots)

def all_roots
  {N : Std.Usize} (p : params.Params) (d : Std.Usize) (hp : Std.Usize)
  (sig_fors : alloc.vec.Vec Std.U8) (md : Slice Std.U8) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (leaf_pks : alloc.vec.Vec (Option (Array Std.U8 N)))
  (leaf_pk_count : Std.Usize) (xmss_auth : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let roots := alloc.vec.Vec.with_capacity (Array Std.U8 N) d
  let s := alloc.vec.Vec.deref sig_fors
  let a ← engine.recover p s md seed fors_addr
  let roots1 ← alloc.vec.Vec.push roots a
  all_roots_loop0
    { start := 0#usize, «end» := leaf_pk_count } p hp seed layers leaf_pks
    xmss_auth roots1
end slhdsa.ParallelRootWalk
