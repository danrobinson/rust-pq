import Cachepath.ConstructorProgram
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa
/-- Extracted `cache.sha2_ops.build_xmss_tree_loop0.body`. -/
@[rust_loop_body]
def cache.sha2_ops.build_xmss_tree_loop0.body
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (iter : core.ops.range.Range Std.Usize)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done nodes)
  | some i =>
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let i1 ← lift (UScalar.cast .U32 i)
    let a1 ← address.Adrs.with_keypair a i1
    let a2 ← wots.wots_pk_gen sk_seed seed a1
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
        Std.U8 N)) nodes i
    let nodes1 := index_mut_back a2
    ok (cont (iter1, nodes1))

/-- Extracted `cache.sha2_ops.build_xmss_tree_loop0`. -/
@[rust_loop]
def cache.sha2_ops.build_xmss_tree_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, nodes1) => cache.sha2_ops.build_xmss_tree_loop0.body sk_seed
      seed adrs iter1 nodes1)
    (iter, nodes)

/-- Extracted `cache.sha2_ops.build_xmss_tree_loop1_loop0.body`. -/
@[rust_loop_body]
def cache.sha2_ops.build_xmss_tree_loop1_loop0.body
  {N : Std.Usize} (seed : hash.Seed N) (adrs : address.Adrs) (z : Std.U32)
  (prev : Std.Usize) (cur : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done nodes)
  | some i =>
    let a ← address.Adrs.with_type adrs address.TREE
    let a1 ← address.Adrs.with_word2 a z
    let i1 ← lift (UScalar.cast .U32 i)
    let a2 ← address.Adrs.with_word3 a1 i1
    let i2 ← 2#usize * i
    let i3 ← prev + i2
    let a3 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) nodes i3
    let i4 ← prev + i2
    let i5 ← i4 + 1#usize
    let a4 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) nodes i5
    let a5 ← xmss.hash2 seed a2 a3 a4
    let i6 ← cur + i
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
        Std.U8 N)) nodes i6
    let nodes1 := index_mut_back a5
    ok (cont (iter1, nodes1))

/-- Extracted `cache.sha2_ops.build_xmss_tree_loop1_loop0`. -/
@[rust_loop]
def cache.sha2_ops.build_xmss_tree_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (seed : hash.Seed N)
  (adrs : address.Adrs) (nodes : alloc.vec.Vec (Array Std.U8 N)) (z : Std.U32)
  (prev : Std.Usize) (cur : Std.Usize) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, nodes1) => cache.sha2_ops.build_xmss_tree_loop1_loop0.body
      seed adrs z prev cur iter1 nodes1)
    (iter, nodes)

/-- Extracted `cache.sha2_ops.build_xmss_tree_loop1.body`. -/
@[rust_loop_body]
def cache.sha2_ops.build_xmss_tree_loop1.body
  {N : Std.Usize} (hp : Std.U32) (seed : hash.Seed N) (adrs : address.Adrs)
  (num_leaves : Std.Usize) (iter : core.ops.range.RangeInclusive Std.U32)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.U32) ×
    (alloc.vec.Vec (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepU32 iter
  match o with
  | none => ok (done nodes)
  | some z =>
    let i ← z - 1#u32
    let prev ← cache.level_offset hp i
    let cur ← cache.level_offset hp z
    let count ← num_leaves >>> z
    let nodes1 ←
      cache.sha2_ops.build_xmss_tree_loop1_loop0
        { start := 0#usize, «end» := count } seed adrs nodes z prev cur
    ok (cont (iter1, nodes1))

/-- Extracted `cache.sha2_ops.build_xmss_tree_loop1`. -/
@[rust_loop]
def cache.sha2_ops.build_xmss_tree_loop1
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.U32) (hp : Std.U32)
  (seed : hash.Seed N) (adrs : address.Adrs) (num_leaves : Std.Usize)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, nodes1) => cache.sha2_ops.build_xmss_tree_loop1.body hp seed
      adrs num_leaves iter1 nodes1)
    (iter, nodes)

/-- Extracted `cache.sha2_ops.build_xmss_tree`. -/
def cache.sha2_ops.build_xmss_tree
  {N : Std.Usize} (hp : Std.U32) (layer : Std.U32) (tree_index : Std.U64)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let seed ← hash.seed_ctx pk_seed
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_layer a layer
  let adrs ← address.Adrs.with_tree a1 tree_index
  let num_leaves ← 1#usize <<< hp
  let total ← cache.tree_node_count hp
  let a2 := Array.repeat N 0#u8
  let nodes ←
    alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a2 total
  let nodes1 ←
    cache.sha2_ops.build_xmss_tree_loop0
      { start := 0#usize, «end» := num_leaves } sk_seed seed adrs nodes
  let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
  cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes1
end slhdsa
