import Cachepath.BuilderShake
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.workers
set_option linter.concreteInstances false
class Pool where
  sha2 {N : Usize} : Usize → Array U8 N → hash.Seed N → address.Adrs → nativeShake.Rows N →
    Result (Bool × nativeShake.Rows N)
  shake {N : Usize} : Usize → Array U8 N → Array U8 N → address.Adrs → nativeShake.Rows N →
    Result (Bool × nativeShake.Rows N)

variable [Pool] [nativeShake.Backend]

/-- Parallel-feature root of the sha2 builder. -/
def sha2Tree
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
  let (s, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice
      (Array Std.U8 N)) nodes { «end» := num_leaves }
  let (built_parallel, s1) ←
    Pool.sha2 num_leaves sk_seed seed adrs s
  if built_parallel
  then
    let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
    let nodes1 := index_mut_back s1
    cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes1
  else
    let nodes1 := index_mut_back s1
    let nodes2 ←
      cache.sha2_ops.build_xmss_tree_loop0
        { start := 0#usize, «end» := num_leaves } sk_seed seed adrs nodes1
    let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
    cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes2

/-- Parallel-feature root of the shake builder. -/
def shakeTree
  {N : Std.Usize} (hp : Std.U32) (layer : Std.U32) (tree_index : Std.U64)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_layer a layer
  let adrs ← address.Adrs.with_tree a1 tree_index
  let num_leaves ← 1#usize <<< hp
  let total ← cache.tree_node_count hp
  let a2 := Array.repeat N 0#u8
  let nodes ←
    alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a2 total
  let (s, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice
      (Array Std.U8 N)) nodes { «end» := num_leaves }
  let (built_parallel, s1) ←
    Pool.shake num_leaves sk_seed pk_seed adrs s
  let nodes1 ←
    if built_parallel
    then ok (index_mut_back s1)
    else
      do
      let nodes2 := index_mut_back s1
      let (s2, index_mut_back1) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice
          (Array Std.U8 N)) nodes2 { «end» := num_leaves }
      let s3 ←
        nativeShake.fill_leaves_chunk sk_seed pk_seed adrs 0#usize s2
      ok (index_mut_back1 s3)
  let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
  nativeShake.build_xmss_tree_loop0 iter hp pk_seed adrs num_leaves nodes1
end slhdsa.cache.builder.workers
