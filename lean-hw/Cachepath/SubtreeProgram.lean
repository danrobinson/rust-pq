import Cachepath.BuilderShake
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.cache.builder.nativeShake.Subtree

class Single where
  leaf {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Result (Array U8 N)

variable [Backend] [Single]

/-- Rust loop body for the cached SIMD subtree. -/
@[rust_loop_body]
def node_loop.body
  {N : Std.Usize} (i : Std.U32) (z : Std.U32) (seed : Array Std.U8 N)
  (addr : address.Adrs) (num_leaves : Std.Usize)
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
  | some h =>
    let count ← num_leaves >>> h
    let i1 ← lift (UScalar.cast .Usize i)
    let i2 ← z - h
    let level_base ← i1 <<< i2
    let a := Array.repeat N 0#u8
    let next ←
      alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a count
    let s := alloc.vec.Vec.deref cur
    let (s1, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut next)
    let s2 ← Backend.pairs seed addr h level_base s s1
    let next1 := deref_mut_back s2
    ok (cont (iter1, next1))

/-- Rust loop for the cached SIMD subtree. -/
@[rust_loop]
def node_loop
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.U32) (i : Std.U32)
  (z : Std.U32) (seed : Array Std.U8 N) (addr : address.Adrs)
  (num_leaves : Std.Usize) (cur : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, cur1) => node_loop.body i z seed
      addr num_leaves iter1 cur1)
    (iter, cur)

/-- Rust entry for the cached SIMD subtree. -/
def node
  {N : Std.Usize} (sk : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if z = 0#u32
  then
    let a ← address.Adrs.with_type addr address.WOTS_HASH
    let a1 ← address.Adrs.with_keypair a i
    Single.leaf sk seed a1
  else
    let num_leaves ← 1#usize <<< z
    if num_leaves <= 512#usize
    then
      let i1 ← lift (UScalar.cast .Usize i)
      let base ← i1 <<< z
      let a := Array.repeat N 0#u8
      let cur ←
        alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a
          num_leaves
      let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut cur)
      let s1 ← Backend.fill sk seed addr base s
      let iter ← core.ops.range.RangeInclusive.new 1#u32 z
      let cur1 := deref_mut_back s1
      let cur2 ←
        node_loop iter i z seed addr num_leaves cur1
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) cur2 0#usize
    else
      let i1 ← 2#u32 * i
      let i2 ← z - 1#u32
      let l ← node sk i1 i2 seed addr
      let i3 ← i1 + 1#u32
      let r ← node sk i3 i2 seed addr
      let a ← address.Adrs.with_type addr address.TREE
      let a1 ← address.Adrs.with_word2 a z
      let a2 ← address.Adrs.with_word3 a1 i
      shake.hash.thash_pair seed a2 l r
partial_fixpoint

end slhdsa.cache.builder.nativeShake.Subtree
