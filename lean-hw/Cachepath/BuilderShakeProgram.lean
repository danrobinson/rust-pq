import Xmsskeys.Funs
import Cachepath.BuilderLayout
import Cachepath.ShakeScalar
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.cache.builder.nativeShake
class Backend where
  available : Usize → Result Bool
  fill {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Usize → Slice (Array U8 N) → Result (Slice (Array U8 N))
  pairs {N : Usize} : Array U8 N → address.Adrs → U32 → Usize → Slice (Array U8 N) → Slice (Array U8 N) → Result (Slice (Array U8 N))

set_option linter.concreteInstances false
variable [Backend]

/-- Extracted `fill_leaves_chunk_loop.body`. -/
@[rust_loop_body]
def fill_leaves_chunk_loop.body
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N)
  (adrs : address.Adrs) (start : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array Std.U8 N)))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array Std.U8 N)) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut (Array Std.U8 N))) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut (Array Std.U8 N))) ×
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array
    Std.U8 N)) → core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut (Array Std.U8 N))))
    (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array
    Std.U8 N))))
  := do
  let (o, iter1, next_back) ←
    XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next
      (XmssKeysRust.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (Array
      Std.U8 N)) iter
  match o with
  | none => ok (done (let e := next_back iter1 none
                      back e))
  | some p =>
    let (k, _) := p
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let i ← start + k
    let i1 ← lift (UScalar.cast .U32 i)
    let a1 ← address.Adrs.with_keypair a i1
    let slot ← CacheScalar.cache.shake_ops.wots_pk_gen_portable sk_seed pk_seed a1
    ok (cont (iter1, fun e => let e1 := next_back e (some (k, slot))
                              back e1))

/-- Extracted `fill_leaves_chunk_loop`. -/
@[rust_loop]
def fill_leaves_chunk_loop
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array Std.U8 N)))
  (back : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
  (Array Std.U8 N)) → core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut (Array Std.U8 N))) (sk_seed : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (adrs : address.Adrs) (start : Std.Usize) :
  Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut
    (Array Std.U8 N)))
  := do
  loop
    (fun (iter1, back1) => fill_leaves_chunk_loop.body sk_seed
      pk_seed adrs start iter1 back1)
    (iter, back)

/-- Extracted `fill_leaves_chunk`. -/
def fill_leaves_chunk
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N)
  (adrs : address.Adrs) (start : Std.Usize) (out : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  let b ← Backend.available N
  if b
  then Backend.fill sk_seed pk_seed adrs start out
  else
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut out
    let (iter, trait_default_back) ←
      XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default
        (XmssKeysRust.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        (Array Std.U8 N)) im
    let back ←
      fill_leaves_chunk_loop iter (fun e => e) sk_seed pk_seed
        adrs start
    let im1 := trait_default_back back
    ok (iter_mut_back im1)

/-- Extracted `build_xmss_tree_loop0_loop0.body`. -/
@[rust_loop_body]
def build_xmss_tree_loop0_loop0.body
  {N : Std.Usize} (pk_seed : Array Std.U8 N) (adrs : address.Adrs)
  (z : Std.U32) (children : Slice (Array Std.U8 N))
  (iter : core.ops.range.Range Std.Usize) (parents : Slice (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice (Array Std.U8
    N))) (Slice (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done parents)
  | some i =>
    let a ← address.Adrs.with_type adrs address.TREE
    let a1 ← address.Adrs.with_word2 a z
    let i1 ← lift (UScalar.cast .U32 i)
    let a2 ← address.Adrs.with_word3 a1 i1
    let i2 ← 2#usize * i
    let a3 ← Slice.index_usize children i2
    let i3 ← i2 + 1#usize
    let a4 ← Slice.index_usize children i3
    let a5 ← shake.hash.thash_pair pk_seed a2 a3 a4
    let s ← Slice.update parents i a5
    ok (cont (iter1, s))

/-- Extracted `build_xmss_tree_loop0_loop0`. -/
@[rust_loop]
def build_xmss_tree_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (pk_seed : Array Std.U8 N) (adrs : address.Adrs) (z : Std.U32)
  (children : Slice (Array Std.U8 N)) (parents : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  loop
    (fun (iter1, parents1) => build_xmss_tree_loop0_loop0.body
      pk_seed adrs z children iter1 parents1)
    (iter, parents)

/-- Extracted `build_xmss_tree_loop0.body`. -/
@[rust_loop_body]
def build_xmss_tree_loop0.body
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
    let b ← Backend.available N
    if b
    then
      let parents1 ←
        Backend.pairs pk_seed adrs z 0#usize children parents
      let parents_slice1 := index_mut_back parents1
      let s1 := split_at_mut_back (children_slice, parents_slice1)
      let nodes1 := deref_mut_back s1
      ok (cont (iter1, nodes1))
    else
      let parents1 ←
        build_xmss_tree_loop0_loop0
          { start := 0#usize, «end» := count } pk_seed adrs z children
          parents
      let parents_slice1 := index_mut_back parents1
      let s1 := split_at_mut_back (children_slice, parents_slice1)
      let nodes1 := deref_mut_back s1
      ok (cont (iter1, nodes1))

/-- Extracted `build_xmss_tree_loop0`. -/
@[rust_loop]
def build_xmss_tree_loop0
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.U32) (hp : Std.U32)
  (pk_seed : Array Std.U8 N) (adrs : address.Adrs) (num_leaves : Std.Usize)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, nodes1) => build_xmss_tree_loop0.body hp
      pk_seed adrs num_leaves iter1 nodes1)
    (iter, nodes)

/-- Extracted `build_xmss_tree`. -/
def build_xmss_tree
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
  let s1 ← fill_leaves_chunk sk_seed pk_seed adrs 0#usize s
  let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
  let nodes1 := index_mut_back s1
  build_xmss_tree_loop0 iter hp pk_seed adrs num_leaves nodes1

end slhdsa.cache.builder.nativeShake
