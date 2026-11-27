import Cachepath.NativeVerify.ForsFused
import Fused.Program
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ForsHorizontal
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance : Machine := Fused.machine kernel

@[reducible]
def subtree.closure (N : Std.Usize) := Std.U32


def
  subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : subtree.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (subtree.closure N))
  := do
  let i ← lift (UScalar.cast .U32 tupled_args)
  let i1 ← c + i
  ok (i1, c)


def
  subtree.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : subtree.closure N)
  (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1


@[reducible]
def
  subtree.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnOnce
  (subtree.closure N) Std.Usize Std.U32 := {
  call_once :=
    subtree.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}


@[reducible]
def
  subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnMut
  (subtree.closure N) Std.Usize Std.U32 := {
  FnOnceInst :=
    subtree.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    N
  call_mut :=
    subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}


@[rust_loop_body]
def subtree_loop0.body
  (node_index : Std.U32) (z : Std.Usize)
  (iter : core.ops.range.RangeInclusive Std.Usize)
  (next_idx : Array Std.U32 16#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Array
    Std.U32 16#usize)) (Array Std.U32 16#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done next_idx)
  | some h =>
    let i ← z - h
    let i1 ← node_index <<< i
    let a ← Array.update next_idx h i1
    ok (cont (iter1, a))


@[rust_loop]
def subtree_loop0
  (iter : core.ops.range.RangeInclusive Std.Usize) (node_index : Std.U32)
  (z : Std.Usize) (next_idx : Array Std.U32 16#usize) :
  Result (Array Std.U32 16#usize)
  := do
  loop
    (fun (iter1, next_idx1) => subtree_loop0.body
      node_index z iter1 next_idx1)
    (iter, next_idx)


@[rust_loop_body]
def subtree_loop1_loop0_loop0.body
  {N : Std.Usize} (tree_adrs : address.Adrs) (base : Std.U32) (lvl : Std.U32)
  (row : Array (Array Std.U8 N) 16#usize)
  (iter : core.ops.range.Range Std.Usize) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize)) ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize)
    × (Array (Array Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (addrs, left, right))
  | some k =>
    let a ← address.Adrs.with_word2 tree_adrs lvl
    let i ← lift (UScalar.cast .U32 k)
    let i1 ← base + i
    let a1 ← address.Adrs.with_word3 a i1
    let a2 ← Array.update addrs k a1
    let i2 ← 2#usize * k
    let a3 ← Array.index_usize row i2
    let a4 ← Array.update left k a3
    let i3 ← i2 + 1#usize
    let a5 ← Array.index_usize row i3
    let a6 ← Array.update right k a5
    ok (cont (iter1, a2, a4, a6))


@[rust_loop]
def subtree_loop1_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (tree_adrs : address.Adrs) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) (base : Std.U32) (lvl : Std.U32)
  (row : Array (Array Std.U8 N) 16#usize) :
  Result ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize) ×
    (Array (Array Std.U8 N) 8#usize))
  := do
  loop
    (fun (iter1, addrs1, left1, right1) =>
      subtree_loop1_loop0_loop0.body tree_adrs base
      lvl row iter1 addrs1 left1 right1)
    (iter, addrs, left, right)


@[rust_loop_body]
def subtree_loop1_loop0.body
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (iter : core.ops.range.Range Std.Usize)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  (len : Array Std.Usize 16#usize) (next_idx : Array Std.U32 16#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array (Array
    Std.U8 N) 16#usize) 16#usize) × (Array Std.Usize 16#usize) × (Array
    Std.U32 16#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) ((Array (Array (Array
    Std.U8 N) 16#usize) 16#usize) × (Array Std.Usize 16#usize) × (Array
    Std.U32 16#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (buf, len, next_idx, addrs, left, right))
  | some h =>
    let i ← Array.index_usize len h
    if i < 16#usize
    then ok (done (buf, len, next_idx, addrs, left, right))
    else
      let i1 ← h + 1#usize
      let base ← Array.index_usize next_idx i1
      let lvl ← lift (UScalar.cast .U32 i1)
      let row ← Array.index_usize buf h
      let (addrs1, left1, right1) ←
        subtree_loop1_loop0_loop0
          { start := 0#usize, «end» := 8#usize } tree_adrs addrs left right
          base lvl row
      let parents ← (ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 8#usize
      let len1 ← Array.update len h 0#usize
      let i2 ← h + 1#usize
      let pdst ← Array.index_usize len1 i2
      let (a, index_mut_back) ← Array.index_mut_usize buf i2
      let i3 ← pdst + 8#usize
      let (s, index_mut_back1) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N))) a
          { start := pdst, «end» := i3 }
      let s1 ← lift (Array.to_slice parents)
      let s2 ←
        core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
          core.marker.CopyU8) s s1
      let a1 ← Array.update len1 i2 i3
      let i4 ← base + 8#u32
      let a2 ← Array.update next_idx i2 i4
      let a3 := index_mut_back1 s2
      let a4 := index_mut_back a3
      ok (cont (iter1, a4, a1, a2, addrs1, left1, right1))


@[rust_loop]
def subtree_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  (len : Array Std.Usize 16#usize) (next_idx : Array Std.U32 16#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result ((Array (Array (Array Std.U8 N) 16#usize) 16#usize) × (Array
    Std.Usize 16#usize) × (Array Std.U32 16#usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize))
  := do
  loop
    (fun (iter1, buf1, len1, next_idx1, addrs1, left1, right1) =>
      subtree_loop1_loop0.body seed tree_adrs iter1
      buf1 len1 next_idx1 addrs1 left1 right1)
    (iter, buf, len, next_idx, addrs, left, right)


@[rust_loop_body]
def subtree_loop1.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (z : Std.Usize) (tree_adrs : address.Adrs) (first_leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  (len : Array Std.Usize 16#usize) (next_idx : Array Std.U32 16#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Array (Array
    Std.U8 N) 16#usize) 16#usize) × (Array Std.Usize 16#usize) × (Array
    Std.U32 16#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) ((Array (Array (Array
    Std.U8 N) 16#usize) 16#usize) × (Array Std.Usize 16#usize) × (Array
    Std.U32 16#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done (buf, len, next_idx, addrs, left, right))
  | some b =>
    let i6 ← b * 8#u32
    let base_leaf ← first_leaf + i6
    let indices ←
      core.array.from_fn 8#usize
        (subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        N) base_leaf
    let leaves ←
      (ForsFused.fused kernel.active) sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } indices 8#usize
    let dst ← Array.index_usize len 0#usize
    let (a, index_mut_back) ← Array.index_mut_usize buf 0#usize
    let i7 ← dst + 8#usize
    let (s, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N))) a
        { start := dst, «end» := i7 }
    let s1 ← lift (Array.to_slice leaves)
    let s2 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
        core.marker.CopyU8) s s1
    let a1 ← Array.update len 0#usize i7
    let a2 := index_mut_back1 s2
    let a3 := index_mut_back a2
    let (buf1, len1, next_idx1, addrs1, left1, right1) ←
      subtree_loop1_loop0
        { start := 0#usize, «end» := z } seed tree_adrs a3 a1 next_idx addrs
        left right
    ok (cont (iter1, buf1, len1, next_idx1, addrs1, left1, right1))


@[rust_loop]
def subtree_loop1
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (z : Std.Usize)
  (tree_adrs : address.Adrs)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  (len : Array Std.Usize 16#usize) (next_idx : Array Std.U32 16#usize)
  (first_leaf : Std.U32) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result ((Array (Array (Array Std.U8 N) 16#usize) 16#usize) × (Array
    Std.Usize 16#usize) × (Array Std.U32 16#usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize))
  := do
  loop
    (fun (iter1, buf1, len1, next_idx1, addrs1, left1, right1) =>
      subtree_loop1.body sk seed i i1 i2 i3 i4 i5 z
      tree_adrs first_leaf iter1 buf1 len1 next_idx1 addrs1 left1 right1)
    (iter, buf, len, next_idx, addrs, left, right)


@[rust_loop_body]
def subtree_loop2_loop0.body
  {N : Std.Usize} (tree_adrs : address.Adrs) (base : Std.U32) (lvl : Std.U32)
  (row : Array (Array Std.U8 N) 16#usize)
  (iter : core.ops.range.Range Std.Usize) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize)) ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize)
    × (Array (Array Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (addrs, left, right))
  | some k =>
    let a ← address.Adrs.with_word2 tree_adrs lvl
    let i ← lift (UScalar.cast .U32 k)
    let i1 ← base + i
    let a1 ← address.Adrs.with_word3 a i1
    let a2 ← Array.update addrs k a1
    let i2 ← 2#usize * k
    let a3 ← Array.index_usize row i2
    let a4 ← Array.update left k a3
    let i3 ← i2 + 1#usize
    let a5 ← Array.index_usize row i3
    let a6 ← Array.update right k a5
    ok (cont (iter1, a2, a4, a6))


@[rust_loop]
def subtree_loop2_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (tree_adrs : address.Adrs) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) (base : Std.U32) (lvl : Std.U32)
  (row : Array (Array Std.U8 N) 16#usize) :
  Result ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize) ×
    (Array (Array Std.U8 N) 8#usize))
  := do
  loop
    (fun (iter1, addrs1, left1, right1) =>
      subtree_loop2_loop0.body tree_adrs base lvl
      row iter1 addrs1 left1 right1)
    (iter, addrs, left, right)


@[rust_loop_body]
def subtree_loop2.body
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (iter : core.ops.range.Range Std.Usize)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  (len : Array Std.Usize 16#usize) (next_idx : Array Std.U32 16#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array (Array
    Std.U8 N) 16#usize) 16#usize) × (Array Std.Usize 16#usize) × (Array
    Std.U32 16#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) (Array (Array (Array
    Std.U8 N) 16#usize) 16#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done buf)
  | some h =>
    let i ← Array.index_usize len h
    let count ← i / 2#usize
    if count = 0#usize
    then ok (cont (iter1, buf, len, next_idx, addrs, left, right))
    else
      let i1 ← h + 1#usize
      let base ← Array.index_usize next_idx i1
      let lvl ← lift (UScalar.cast .U32 i1)
      if count = 1#usize
      then
        let a ← address.Adrs.with_word2 tree_adrs lvl
        let parent_adrs ← address.Adrs.with_word3 a base
        let a1 ← Array.index_usize buf h
        let a2 ← Array.index_usize a1 0#usize
        let a3 ← Array.index_usize a1 1#usize
        let p ← shake.hash.thash_pair seed parent_adrs a2 a3
        let pdst ← Array.index_usize len i1
        let (a4, index_mut_back) ← Array.index_mut_usize buf i1
        let a5 ← Array.update a4 pdst p
        let i2 ← pdst + 1#usize
        let len1 ← Array.update len i1 i2
        let i3 ← base + 1#u32
        let a6 ← Array.update next_idx i1 i3
        let a7 ← Array.update len1 h 0#usize
        let a8 := index_mut_back a5
        ok (cont (iter1, a8, a7, a6, addrs, left, right))
      else
        let row ← Array.index_usize buf h
        let (addrs1, left1, right1) ←
          subtree_loop2_loop0
            { start := 0#usize, «end» := count } tree_adrs addrs left right
            base lvl row
        let parents ← (ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 count
        let i2 ← h + 1#usize
        let pdst ← Array.index_usize len i2
        let (a, index_mut_back) ← Array.index_mut_usize buf i2
        let i3 ← pdst + count
        let (s, index_mut_back1) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N))) a
            { start := pdst, «end» := i3 }
        let s1 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            parents { «end» := count }
        let s2 ←
          core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
            core.marker.CopyU8) s s1
        let len1 ← Array.update len i2 i3
        let i4 ← lift (UScalar.cast .U32 count)
        let i5 ← base + i4
        let a1 ← Array.update next_idx i2 i5
        let a2 ← Array.update len1 h 0#usize
        let a3 := index_mut_back1 s2
        let a4 := index_mut_back a3
        ok (cont (iter1, a4, a2, a1, addrs1, left1, right1))


@[rust_loop]
def subtree_loop2
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  (len : Array Std.Usize 16#usize) (next_idx : Array Std.U32 16#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (Array (Array (Array Std.U8 N) 16#usize) 16#usize)
  := do
  loop
    (fun (iter1, buf1, len1, next_idx1, addrs1, left1, right1) =>
      subtree_loop2.body seed tree_adrs iter1 buf1
      len1 next_idx1 addrs1 left1 right1)
    (iter, buf, len, next_idx, addrs, left, right)


def subtree
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (node_index : Std.U32) (height : Std.U32) :
  Result (Array Std.U8 N)
  := do
  let z ← lift (UScalar.cast .Usize height)
  massert (z <= 15#usize)
  let a ← address.Adrs.with_type addr address.FORS_TREE
  let tree_adrs ← address.Adrs.with_keypair a addr.keypair
  let a1 := Array.repeat N 0#u8
  let a2 := Array.repeat 16#usize a1
  let buf := Array.repeat 16#usize a2
  let len := Array.repeat 16#usize 0#usize
  let next_idx := Array.repeat 16#usize 0#u32
  let iter ← core.ops.range.RangeInclusive.new 0#usize z
  let next_idx1 ←
    subtree_loop0 iter node_index z next_idx
  let i ← height - 3#u32
  let blocks ← 1#u32 <<< i
  let first_leaf ← node_index <<< height
  let addrs := Array.repeat 8#usize tree_adrs
  let a3 := Array.repeat N 0#u8
  let left := Array.repeat 8#usize a3
  let a4 := Array.repeat N 0#u8
  let right := Array.repeat 8#usize a4
  let (buf1, len1, next_idx2, addrs1, left1, right1) ←
    subtree_loop1
      { start := 0#u32, «end» := blocks } sk seed addr.layer addr.tree
      addr.typ addr.keypair addr.word2 addr.word3 z tree_adrs buf len next_idx1
      first_leaf addrs left right
  let buf2 ←
    subtree_loop2
      { start := 0#usize, «end» := z } seed tree_adrs buf1 len1 next_idx2
      addrs1 left1 right1
  let a5 ← Array.index_usize buf2 z
  Array.index_usize a5 0#usize

end slhdsa.ForsHorizontal
