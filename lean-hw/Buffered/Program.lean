import Cachepath.NativeVerify.ActiveHashes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Buffered
open ShakeBatch NativeVerify

abbrev Rows8 (N : Usize) := Array (Array U8 N) 8#usize
abbrev Row16 (N : Usize) := Array (Array U8 N) 16#usize
class Kernel where
  active : Matrix 8#usize → Usize → Result (Matrix 8#usize)
  leaves {N : Usize} : Array U8 N → Array U8 N → U32 → address.Adrs → Result (Rows8 N)
  small {N : Usize} (K : Usize) : Array U8 N → Array U8 N → U32 → address.Adrs → Result (Array (Array U8 N) K)
  fallback {N : Usize} : Array U8 N → Array U8 N → U32 → U32 → address.Adrs → Result (Array U8 N)

def machine (k : Kernel) : Machine := ⟨8#usize, fun s => k.active s 8#usize⟩
variable [kernel : Kernel]
local instance bufferedMachine : Machine := machine kernel
@[rust_loop_body]
def subtree_loop0.body
  {N : Std.Usize} (tree_index : Std.U32) (tree_adrs : address.Adrs)
  (leaves : Array (Array Std.U8 N) 4#usize)
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
    let a ← address.Adrs.with_word2 tree_adrs 1#u32
    let i ← tree_index * 2#u32
    let i1 ← lift (UScalar.cast .U32 k)
    let i2 ← i + i1
    let a1 ← address.Adrs.with_word3 a i2
    let a2 ← Array.update addrs k a1
    let i3 ← 2#usize * k
    let a3 ← Array.index_usize leaves i3
    let a4 ← Array.update left k a3
    let i4 ← i3 + 1#usize
    let a5 ← Array.index_usize leaves i4
    let a6 ← Array.update right k a5
    ok (cont (iter1, a2, a4, a6))

@[rust_loop]
def subtree_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (tree_index : Std.U32) (tree_adrs : address.Adrs)
  (leaves : Array (Array Std.U8 N) 4#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize) ×
    (Array (Array Std.U8 N) 8#usize))
  := do
  loop
    (fun (iter1, addrs1, left1, right1) => subtree_loop0.body
      tree_index tree_adrs leaves iter1 addrs1 left1 right1)
    (iter, addrs, left, right)

@[rust_loop_body]
def subtree_loop1.body
  (tree_index : Std.U32) (z : Std.Usize)
  (iter : core.ops.range.RangeInclusive Std.Usize)
  (next_idx : Array Std.U32 17#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Array
    Std.U32 17#usize)) (Array Std.U32 17#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done next_idx)
  | some h =>
    let i ← z - h
    let i1 ← tree_index <<< i
    let a ← Array.update next_idx h i1
    ok (cont (iter1, a))

@[rust_loop]
def subtree_loop1
  (iter : core.ops.range.RangeInclusive Std.Usize) (tree_index : Std.U32)
  (z : Std.Usize) (next_idx : Array Std.U32 17#usize) :
  Result (Array Std.U32 17#usize)
  := do
  loop
    (fun (iter1, next_idx1) => subtree_loop1.body tree_index z
      iter1 next_idx1)
    (iter, next_idx)

@[rust_loop_body]
def subtree_loop2_loop0_loop0.body
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
def subtree_loop2_loop0_loop0
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
      subtree_loop2_loop0_loop0.body tree_adrs base lvl row
      iter1 addrs1 left1 right1)
    (iter, addrs, left, right)

@[rust_loop_body]
def subtree_loop2_loop0.body
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (iter : core.ops.range.Range Std.Usize)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  (len : Array Std.Usize 17#usize) (next_idx : Array Std.U32 17#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array (Array
    Std.U8 N) 16#usize) 17#usize) × (Array Std.Usize 17#usize) × (Array
    Std.U32 17#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) ((Array (Array (Array
    Std.U8 N) 16#usize) 17#usize) × (Array Std.Usize 17#usize) × (Array
    Std.U32 17#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
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
        subtree_loop2_loop0_loop0
          { start := 0#usize, «end» := 8#usize } tree_adrs addrs left right
          base lvl row
      let parents ← (NativeVerify.ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 8#usize
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
def subtree_loop2_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  (len : Array Std.Usize 17#usize) (next_idx : Array Std.U32 17#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result ((Array (Array (Array Std.U8 N) 16#usize) 17#usize) × (Array
    Std.Usize 17#usize) × (Array Std.U32 17#usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize))
  := do
  loop
    (fun (iter1, buf1, len1, next_idx1, addrs1, left1, right1) =>
      subtree_loop2_loop0.body seed tree_adrs iter1 buf1 len1
      next_idx1 addrs1 left1 right1)
    (iter, buf, len, next_idx, addrs, left, right)

@[rust_loop_body]
def subtree_loop2.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (tree_adrs : address.Adrs) (z : Std.Usize)
  (first_leaf : Std.U32) (iter : core.ops.range.Range Std.U32)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  (len : Array Std.Usize 17#usize) (next_idx : Array Std.U32 17#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Array (Array
    Std.U8 N) 16#usize) 17#usize) × (Array Std.Usize 17#usize) × (Array
    Std.U32 17#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) ((Array (Array (Array
    Std.U8 N) 16#usize) 17#usize) × (Array Std.Usize 17#usize) × (Array
    Std.U32 17#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done (buf, len, next_idx, addrs, left, right))
  | some b =>
    let i ← b * 8#u32
    let i1 ← first_leaf + i
    let leaves ← kernel.leaves sk seed i1 addr
    let dst ← Array.index_usize len 0#usize
    let (a, index_mut_back) ← Array.index_mut_usize buf 0#usize
    let i2 ← dst + 8#usize
    let (s, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N))) a
        { start := dst, «end» := i2 }
    let s1 ← lift (Array.to_slice leaves)
    let s2 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
        core.marker.CopyU8) s s1
    let a1 ← Array.update len 0#usize i2
    let a2 := index_mut_back1 s2
    let a3 := index_mut_back a2
    let (buf1, len1, next_idx1, addrs1, left1, right1) ←
      subtree_loop2_loop0 { start := 0#usize, «end» := z }
        seed tree_adrs a3 a1 next_idx addrs left right
    ok (cont (iter1, buf1, len1, next_idx1, addrs1, left1, right1))

@[rust_loop]
def subtree_loop2
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (addr : address.Adrs) (tree_adrs : address.Adrs)
  (z : Std.Usize) (buf : Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  (len : Array Std.Usize 17#usize) (next_idx : Array Std.U32 17#usize)
  (first_leaf : Std.U32) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result ((Array (Array (Array Std.U8 N) 16#usize) 17#usize) × (Array
    Std.Usize 17#usize) × (Array Std.U32 17#usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize))
  := do
  loop
    (fun (iter1, buf1, len1, next_idx1, addrs1, left1, right1) =>
      subtree_loop2.body sk seed addr tree_adrs z first_leaf
      iter1 buf1 len1 next_idx1 addrs1 left1 right1)
    (iter, buf, len, next_idx, addrs, left, right)

@[rust_loop_body]
def subtree_loop3_loop0.body
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
def subtree_loop3_loop0
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
      subtree_loop3_loop0.body tree_adrs base lvl row iter1
      addrs1 left1 right1)
    (iter, addrs, left, right)

@[rust_loop_body]
def subtree_loop3.body
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (iter : core.ops.range.Range Std.Usize)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  (len : Array Std.Usize 17#usize) (next_idx : Array Std.U32 17#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array (Array
    Std.U8 N) 16#usize) 17#usize) × (Array Std.Usize 17#usize) × (Array
    Std.U32 17#usize) × (Array address.Adrs 8#usize) × (Array (Array Std.U8
    N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) (Array (Array (Array
    Std.U8 N) 16#usize) 17#usize))
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
          subtree_loop3_loop0
            { start := 0#usize, «end» := count } tree_adrs addrs left right
            base lvl row
        let parents ← (NativeVerify.ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 count
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
def subtree_loop3
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (buf : Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  (len : Array Std.Usize 17#usize) (next_idx : Array Std.U32 17#usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (Array (Array (Array Std.U8 N) 16#usize) 17#usize)
  := do
  loop
    (fun (iter1, buf1, len1, next_idx1, addrs1, left1, right1) =>
      subtree_loop3.body seed tree_adrs iter1 buf1 len1
      next_idx1 addrs1 left1 right1)
    (iter, buf, len, next_idx, addrs, left, right)

def subtree
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (tree_index : Std.U32) (height : Std.U32) (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← (ok 8#usize : Result Usize)
  if i != 8#usize
  then kernel.fallback sk seed tree_index height addr
  else
    let tree_adrs ← address.Adrs.with_type addr address.TREE
    let z ← lift (UScalar.cast .Usize height)
    massert ((height = 1#u32) || ((height = 2#u32) || (z <= 16#usize)))
    if height = 1#u32
    then
      let i1 ← tree_index * 2#u32
      let leaves ← kernel.small 2#usize sk seed i1 addr
      let a ← address.Adrs.with_word2 tree_adrs 1#u32
      let parent ← address.Adrs.with_word3 a tree_index
      let a1 ← Array.index_usize leaves 0#usize
      let a2 ← Array.index_usize leaves 1#usize
      shake.hash.thash_pair seed parent a1 a2
    else
      if height = 2#u32
      then
        let i1 ← tree_index * 4#u32
        let leaves ← kernel.small 4#usize sk seed i1 addr
        let addrs := Array.repeat 8#usize tree_adrs
        let a := Array.repeat N 0#u8
        let left := Array.repeat 8#usize a
        let a1 := Array.repeat N 0#u8
        let right := Array.repeat 8#usize a1
        let (addrs1, left1, right1) ←
          subtree_loop0
            { start := 0#usize, «end» := 2#usize } tree_index tree_adrs
            leaves addrs left right
        let lvl1 ← (NativeVerify.ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 2#usize
        let a2 ← address.Adrs.with_word2 tree_adrs 2#u32
        let root_adrs ← address.Adrs.with_word3 a2 tree_index
        let a3 ← Array.index_usize lvl1 0#usize
        let a4 ← Array.index_usize lvl1 1#usize
        shake.hash.thash_pair seed root_adrs a3 a4
      else
        let a := Array.repeat N 0#u8
        let a1 := Array.repeat 16#usize a
        let buf := Array.repeat 17#usize a1
        let len := Array.repeat 17#usize 0#usize
        let next_idx := Array.repeat 17#usize 0#u32
        let iter ← core.ops.range.RangeInclusive.new 0#usize z
        let next_idx1 ←
          subtree_loop1 iter tree_index z next_idx
        let i1 ← height - 3#u32
        let blocks ← 1#u32 <<< i1
        let first_leaf ← tree_index <<< height
        let addrs := Array.repeat 8#usize tree_adrs
        let a2 := Array.repeat N 0#u8
        let left := Array.repeat 8#usize a2
        let a3 := Array.repeat N 0#u8
        let right := Array.repeat 8#usize a3
        let (buf1, len1, next_idx2, addrs1, left1, right1) ←
          subtree_loop2 { start := 0#u32, «end» := blocks }
            sk seed addr tree_adrs z buf len next_idx1 first_leaf addrs left
            right
        let buf2 ←
          subtree_loop3 { start := 0#usize, «end» := z }
            seed tree_adrs buf1 len1 next_idx2 addrs1 left1 right1
        let a4 ← Array.index_usize buf2 z
        Array.index_usize a4 0#usize
end slhdsa.Buffered
