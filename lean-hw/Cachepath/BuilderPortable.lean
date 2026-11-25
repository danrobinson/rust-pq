import Cachepath.BuilderShake
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.nativeShake

/-! The RISC-V target compiles out both SIMD branches. These two declarations are
matched to that extraction; the remaining generated loop bodies are shared. -/

/-- Extracted scalar `fill_leaves_chunk`. -/
def portableLeaves
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N)
  (adrs : address.Adrs) (start : Std.Usize) (out : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut out
  let (iter, trait_default_back) ←
    XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default
      (XmssKeysRust.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (Array
      Std.U8 N)) im
  let back ←
    fill_leaves_chunk_loop iter (fun e => e) sk_seed pk_seed
      adrs start
  let im1 := trait_default_back back
  ok (iter_mut_back im1)

/-- Extracted scalar `build_xmss_tree_loop0.body`. -/
@[rust_loop_body]
def portableLevel
  {N : Std.Usize} (hp : Std.U32) (pk_seed : Array Std.U8 N)
  (adrs : address.Adrs) (num_leaves : Std.Usize)
  (iter : core.ops.range.RangeInclusive Std.U32)
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
    let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut nodes)
    let ((children_slice, parents_slice), split_at_mut_back) ←
      core.slice.Slice.split_at_mut s cur
    let i1 ← 2#usize * count
    let i2 ← prev + i1
    let children ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        (Array Std.U8 N)) children_slice { start := prev, «end» := i2 }
    let (parents, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))
        parents_slice { «end» := count }
    let parents1 ←
      build_xmss_tree_loop0_loop0
        { start := 0#usize, «end» := count } pk_seed adrs z children parents
    let parents_slice1 := index_mut_back parents1
    let s1 := split_at_mut_back (children_slice, parents_slice1)
    let nodes1 := deref_mut_back s1
    ok (cont (iter1, nodes1))

theorem portable_leaves_eq {N : Usize} :
    @fill_leaves_chunk scalar N = @portableLeaves N := by
  funext sk pk a start nodes
  have select : @Backend.available scalar N = ok false := rfl
  simp [fill_leaves_chunk,portableLeaves,select,bind_ok]

theorem portable_level_eq {N : Usize} :
    @build_xmss_tree_loop0.body scalar N = @portableLevel N := by
  funext hp pk a leaves it v
  have select : @Backend.available scalar N = ok false := rfl
  simp [build_xmss_tree_loop0.body,portableLevel,select,bind_ok]
  congr 1

end slhdsa.cache.builder.nativeShake
