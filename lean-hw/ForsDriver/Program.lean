import Cachepath.NativeVerify.ForsWideRowsProgram
import Cachepath.NativeVerify.ForsSignNarrow
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance driverMachine : Machine := Fused.machine kernel
class Trees where
  node {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)
  fallback {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Array U32 8#usize → U32 → Usize → Result (Array (Array U8 N) 8#usize)
variable [trees : Trees]

@[rust_loop_body]
def sign_loop2.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (idx0 : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    35#usize)) (Array Std.U32 35#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done idx0)
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← lift (i3 ^^^ 1#u32)
    let a1 ← Array.update idx0 tree i4
    ok (cont (iter1, a1))


@[rust_loop]
def sign_loop2
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (idx0 : Array Std.U32 35#usize) :
  Result (Array Std.U32 35#usize)
  := do
  loop
    (fun (iter1, idx01) => sign_loop2.body selections a iter1
      idx01)
    (iter, idx0)


@[rust_loop_body]
def sign_loop3.body
  {N : Std.Usize} (stride : Std.Usize) (out0 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let pos ← i + N
    let i1 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i1 }
    let a ← Array.index_usize out0 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop3
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (out0 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop3.body stride out0 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop4.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 70#usize)
  (node_idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    70#usize) × (Array Std.U32 35#usize)) ((Array Std.U32 70#usize) × (Array
    Std.U32 35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (leaf_idx, node_idx))
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← i3 >>> 1#i32
    let sib ← lift (i4 ^^^ 1#u32)
    let a1 ← Array.update node_idx tree sib
    let i5 ← 2#u32 * sib
    let i6 ← 2#usize * tree
    let leaf_idx1 ← Array.update leaf_idx i6 i5
    let i7 ← i5 + 1#u32
    let i8 ← i6 + 1#usize
    let a2 ← Array.update leaf_idx1 i8 i7
    ok (cont (iter1, a2, a1))


@[rust_loop]
def sign_loop4
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (leaf_idx : Array Std.U32 70#usize)
  (node_idx : Array Std.U32 35#usize) :
  Result ((Array Std.U32 70#usize) × (Array Std.U32 35#usize))
  := do
  loop
    (fun (iter1, leaf_idx1, node_idx1) => sign_loop4.body
      selections a iter1 leaf_idx1 node_idx1)
    (iter, leaf_idx, node_idx)


@[rust_loop_body]
def sign_loop5.body
  {N : Std.Usize} (stride : Std.Usize) (lvl1 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let i1 ← 2#usize * N
    let pos ← i + i1
    let i2 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i2 }
    let a ← Array.index_usize lvl1 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop5
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (lvl1 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop5.body stride lvl1 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop6_loop0.body
  (tree : Std.Usize) (sib : Std.U32) (iter : core.ops.range.Range Std.Usize)
  (leaf_idx : Array Std.U32 140#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize)) (Array Std.U32 140#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done leaf_idx)
  | some c =>
    let i ← 4#u32 * sib
    let i1 ← lift (UScalar.cast .U32 c)
    let i2 ← i + i1
    let i3 ← 4#usize * tree
    let i4 ← i3 + c
    let a ← Array.update leaf_idx i4 i2
    ok (cont (iter1, a))


@[rust_loop]
def sign_loop6_loop0
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (tree : Std.Usize) (sib : Std.U32) :
  Result (Array Std.U32 140#usize)
  := do
  loop
    (fun (iter1, leaf_idx1) => sign_loop6_loop0.body tree sib
      iter1 leaf_idx1)
    (iter, leaf_idx)


@[rust_loop_body]
def sign_loop6.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize) × (Array Std.U32 70#usize) × (Array Std.U32 35#usize)) ((Array
    Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array Std.U32
    35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (leaf_idx, n1_idx, n2_idx))
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← i3 >>> 2#i32
    let sib ← lift (i4 ^^^ 1#u32)
    let a1 ← Array.update n2_idx tree sib
    let i5 ← 2#u32 * sib
    let i6 ← 2#usize * tree
    let n1_idx1 ← Array.update n1_idx i6 i5
    let i7 ← i5 + 1#u32
    let i8 ← i6 + 1#usize
    let a2 ← Array.update n1_idx1 i8 i7
    let leaf_idx1 ←
      sign_loop6_loop0
        { start := 0#usize, «end» := 4#usize } leaf_idx tree sib
    ok (cont (iter1, leaf_idx1, a2, a1))


@[rust_loop]
def sign_loop6
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result ((Array Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array
    Std.U32 35#usize))
  := do
  loop
    (fun (iter1, leaf_idx1, n1_idx1, n2_idx1) =>
      sign_loop6.body selections a iter1 leaf_idx1 n1_idx1
      n2_idx1)
    (iter, leaf_idx, n1_idx, n2_idx)


@[rust_loop_body]
def sign_loop7.body
  {N : Std.Usize} (stride : Std.Usize) (lvl2 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let i1 ← 3#usize * N
    let pos ← i + i1
    let i2 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i2 }
    let a ← Array.index_usize lvl2 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop7
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (lvl2 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop7.body stride lvl2 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop8_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop8_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop8_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop8.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop8_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop8
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop8.body selections sk seed i
      i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop9_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop9_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop9_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop9.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop9_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop9
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop9.body selections sk seed i
      i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop10_loop0.body
  (tree : Std.Usize) (sib : Std.U32) (iter : core.ops.range.Range Std.Usize)
  (leaf_idx : Array Std.U32 140#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize)) (Array Std.U32 140#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done leaf_idx)
  | some c =>
    let i ← 4#u32 * sib
    let i1 ← lift (UScalar.cast .U32 c)
    let i2 ← i + i1
    let i3 ← 4#usize * tree
    let i4 ← i3 + c
    let a ← Array.update leaf_idx i4 i2
    ok (cont (iter1, a))


@[rust_loop]
def sign_loop10_loop0
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (tree : Std.Usize) (sib : Std.U32) :
  Result (Array Std.U32 140#usize)
  := do
  loop
    (fun (iter1, leaf_idx1) => sign_loop10_loop0.body tree sib
      iter1 leaf_idx1)
    (iter, leaf_idx)


@[rust_loop_body]
def sign_loop10.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize) × (Array Std.U32 70#usize) × (Array Std.U32 35#usize)) ((Array
    Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array Std.U32
    35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (leaf_idx, n1_idx, n2_idx))
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← i3 >>> 2#i32
    let sib ← lift (i4 ^^^ 1#u32)
    let a1 ← Array.update n2_idx tree sib
    let i5 ← 2#u32 * sib
    let i6 ← 2#usize * tree
    let n1_idx1 ← Array.update n1_idx i6 i5
    let i7 ← i5 + 1#u32
    let i8 ← i6 + 1#usize
    let a2 ← Array.update n1_idx1 i8 i7
    let leaf_idx1 ←
      sign_loop10_loop0
        { start := 0#usize, «end» := 4#usize } leaf_idx tree sib
    ok (cont (iter1, leaf_idx1, a2, a1))


@[rust_loop]
def sign_loop10
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result ((Array Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array
    Std.U32 35#usize))
  := do
  loop
    (fun (iter1, leaf_idx1, n1_idx1, n2_idx1) =>
      sign_loop10.body selections a iter1 leaf_idx1 n1_idx1
      n2_idx1)
    (iter, leaf_idx, n1_idx, n2_idx)


@[rust_loop_body]
def sign_loop11.body
  {N : Std.Usize} (stride : Std.Usize) (lvl2 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let i1 ← 3#usize * N
    let pos ← i + i1
    let i2 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i2 }
    let a ← Array.index_usize lvl2 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop11
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (lvl2 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop11.body stride lvl2 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop12_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop12_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop12_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop12.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop12_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop12
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop12.body selections sk seed
      i i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop13_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop13_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop13_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop13.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop13_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop13
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop13.body selections sk seed
      i i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop14.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 70#usize)
  (node_idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    70#usize) × (Array Std.U32 35#usize)) ((Array Std.U32 70#usize) × (Array
    Std.U32 35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (leaf_idx, node_idx))
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← i3 >>> 1#i32
    let sib ← lift (i4 ^^^ 1#u32)
    let a1 ← Array.update node_idx tree sib
    let i5 ← 2#u32 * sib
    let i6 ← 2#usize * tree
    let leaf_idx1 ← Array.update leaf_idx i6 i5
    let i7 ← i5 + 1#u32
    let i8 ← i6 + 1#usize
    let a2 ← Array.update leaf_idx1 i8 i7
    ok (cont (iter1, a2, a1))


@[rust_loop]
def sign_loop14
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (leaf_idx : Array Std.U32 70#usize)
  (node_idx : Array Std.U32 35#usize) :
  Result ((Array Std.U32 70#usize) × (Array Std.U32 35#usize))
  := do
  loop
    (fun (iter1, leaf_idx1, node_idx1) => sign_loop14.body
      selections a iter1 leaf_idx1 node_idx1)
    (iter, leaf_idx, node_idx)


@[rust_loop_body]
def sign_loop15.body
  {N : Std.Usize} (stride : Std.Usize) (lvl1 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let i1 ← 2#usize * N
    let pos ← i + i1
    let i2 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i2 }
    let a ← Array.index_usize lvl1 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop15
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (lvl1 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop15.body stride lvl1 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop16_loop0.body
  (tree : Std.Usize) (sib : Std.U32) (iter : core.ops.range.Range Std.Usize)
  (leaf_idx : Array Std.U32 140#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize)) (Array Std.U32 140#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done leaf_idx)
  | some c =>
    let i ← 4#u32 * sib
    let i1 ← lift (UScalar.cast .U32 c)
    let i2 ← i + i1
    let i3 ← 4#usize * tree
    let i4 ← i3 + c
    let a ← Array.update leaf_idx i4 i2
    ok (cont (iter1, a))


@[rust_loop]
def sign_loop16_loop0
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (tree : Std.Usize) (sib : Std.U32) :
  Result (Array Std.U32 140#usize)
  := do
  loop
    (fun (iter1, leaf_idx1) => sign_loop16_loop0.body tree sib
      iter1 leaf_idx1)
    (iter, leaf_idx)


@[rust_loop_body]
def sign_loop16.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize) × (Array Std.U32 70#usize) × (Array Std.U32 35#usize)) ((Array
    Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array Std.U32
    35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (leaf_idx, n1_idx, n2_idx))
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← i3 >>> 2#i32
    let sib ← lift (i4 ^^^ 1#u32)
    let a1 ← Array.update n2_idx tree sib
    let i5 ← 2#u32 * sib
    let i6 ← 2#usize * tree
    let n1_idx1 ← Array.update n1_idx i6 i5
    let i7 ← i5 + 1#u32
    let i8 ← i6 + 1#usize
    let a2 ← Array.update n1_idx1 i8 i7
    let leaf_idx1 ←
      sign_loop16_loop0
        { start := 0#usize, «end» := 4#usize } leaf_idx tree sib
    ok (cont (iter1, leaf_idx1, a2, a1))


@[rust_loop]
def sign_loop16
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result ((Array Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array
    Std.U32 35#usize))
  := do
  loop
    (fun (iter1, leaf_idx1, n1_idx1, n2_idx1) =>
      sign_loop16.body selections a iter1 leaf_idx1 n1_idx1
      n2_idx1)
    (iter, leaf_idx, n1_idx, n2_idx)


@[rust_loop_body]
def sign_loop17.body
  {N : Std.Usize} (stride : Std.Usize) (lvl2 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let i1 ← 3#usize * N
    let pos ← i + i1
    let i2 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i2 }
    let a ← Array.index_usize lvl2 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop17
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (lvl2 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop17.body stride lvl2 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop18_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop18_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop18_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop18.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop18_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop18
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop18.body selections sk seed
      i i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop19_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop19_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop19_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop19.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop19_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop19
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop19.body selections sk seed
      i i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop20_loop0.body
  (tree : Std.Usize) (sib : Std.U32) (iter : core.ops.range.Range Std.Usize)
  (leaf_idx : Array Std.U32 140#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize)) (Array Std.U32 140#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done leaf_idx)
  | some c =>
    let i ← 4#u32 * sib
    let i1 ← lift (UScalar.cast .U32 c)
    let i2 ← i + i1
    let i3 ← 4#usize * tree
    let i4 ← i3 + c
    let a ← Array.update leaf_idx i4 i2
    ok (cont (iter1, a))


@[rust_loop]
def sign_loop20_loop0
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (tree : Std.Usize) (sib : Std.U32) :
  Result (Array Std.U32 140#usize)
  := do
  loop
    (fun (iter1, leaf_idx1) => sign_loop20_loop0.body tree sib
      iter1 leaf_idx1)
    (iter, leaf_idx)


@[rust_loop_body]
def sign_loop20.body
  (selections : Slice Std.U32) (a : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    140#usize) × (Array Std.U32 70#usize) × (Array Std.U32 35#usize)) ((Array
    Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array Std.U32
    35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (leaf_idx, n1_idx, n2_idx))
  | some tree =>
    let i ← lift (UScalar.cast .U32 tree)
    let i1 ← i <<< a
    let i2 ← Slice.index_usize selections tree
    let i3 ← i1 + i2
    let i4 ← i3 >>> 2#i32
    let sib ← lift (i4 ^^^ 1#u32)
    let a1 ← Array.update n2_idx tree sib
    let i5 ← 2#u32 * sib
    let i6 ← 2#usize * tree
    let n1_idx1 ← Array.update n1_idx i6 i5
    let i7 ← i5 + 1#u32
    let i8 ← i6 + 1#usize
    let a2 ← Array.update n1_idx1 i8 i7
    let leaf_idx1 ←
      sign_loop20_loop0
        { start := 0#usize, «end» := 4#usize } leaf_idx tree sib
    ok (cont (iter1, leaf_idx1, a2, a1))


@[rust_loop]
def sign_loop20
  (iter : core.ops.range.Range Std.Usize) (selections : Slice Std.U32)
  (a : Std.U32) (leaf_idx : Array Std.U32 140#usize)
  (n1_idx : Array Std.U32 70#usize) (n2_idx : Array Std.U32 35#usize) :
  Result ((Array Std.U32 140#usize) × (Array Std.U32 70#usize) × (Array
    Std.U32 35#usize))
  := do
  loop
    (fun (iter1, leaf_idx1, n1_idx1, n2_idx1) =>
      sign_loop20.body selections a iter1 leaf_idx1 n1_idx1
      n2_idx1)
    (iter, leaf_idx, n1_idx, n2_idx)


@[rust_loop_body]
def sign_loop21.body
  {N : Std.Usize} (stride : Std.Usize) (lvl2 : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i ← tree * stride
    let i1 ← 3#usize * N
    let pos ← i + i1
    let i2 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i2 }
    let a ← Array.index_usize lvl2 tree
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop21
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (lvl2 : Array (Array Std.U8 N) 35#usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop21.body stride lvl2 iter1
      sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop22_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop22_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop22_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop22.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop22_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop22
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop22.body selections sk seed
      i i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop23_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (tree : Std.Usize) (leaf : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i6 ← leaf >>> j
    let sib ← lift (i6 ^^^ 1#u32)
    let node ←
      trees.node sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } sib j
    let i7 ← tree * stride
    let i8 ← lift (UScalar.cast .Usize j)
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let pos ← i7 + i10
    let i11 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i11 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop23_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.Usize) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop23_loop0.body sk seed i i1
      i2 i3 i4 i5 stride tree leaf iter1 sig1)
    (iter, sig)


@[rust_loop_body]
def sign_loop23.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (a : Std.U32)
  (stride : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some tree =>
    let i6 ← lift (UScalar.cast .U32 tree)
    let i7 ← i6 <<< a
    let i8 ← Slice.index_usize selections tree
    let leaf ← i7 + i8
    let sig1 ←
      sign_loop23_loop0 { start := 3#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig tree leaf
    ok (cont (iter1, sig1))


@[rust_loop]
def sign_loop23
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop23.body selections sk seed
      i i1 i2 i3 i4 i5 a stride iter1 sig1)
    (iter, sig)


def sign
  {N : Std.Usize} (p : params.Params) (selections : Slice Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let k := Slice.len selections
  let i ← lift (UScalar.cast .Usize p.a)
  let i1 ← i + 1#usize
  let stride ← i1 * N
  let i2 ← k * stride
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i2
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let prf ← address.Adrs.with_keypair a addr.keypair
  let a1 ← address.Adrs.with_type addr address.FORS_TREE
  let tree_adrs ← address.Adrs.with_keypair a1 addr.keypair
  let sig1 ←
    ForsSign.sign_loop0 (ActiveHash.short_active kernel.active) selections sk seed k p.a stride sig prf 0#usize
  massert ((8#usize != 8#usize) || (k <= params.K_MAX))
  if 8#usize != 8#usize
  then
    let iter ←
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := k } 8#usize
    ForsSign.sign_loop1 trees.fallback iter selections sk seed addr.layer addr.tree
      addr.typ addr.keypair addr.word2 addr.word3 k p.a stride sig1
  else
    if p.a > 0#u32
    then
      let idx0 := Array.repeat 35#usize 0#u32
      let idx01 ←
        sign_loop2 { start := 0#usize, «end» := k }
          selections p.a idx0
      let a2 := Array.repeat N 0#u8
      let out0 := Array.repeat 35#usize a2
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) idx01
          { «end» := k }
      let (s1, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) out0
          { «end» := k }
      let s2 ← ForsWideRows.leaves sk seed addr s s1
      let out01 := index_mut_back s2
      let sig2 ←
        sign_loop3 { start := 0#usize, «end» := k } stride
          sig1 out01
      if p.a > 1#u32
      then
        let leaf_idx := Array.repeat 70#usize 0#u32
        let node_idx := Array.repeat 35#usize 0#u32
        let (leaf_idx1, node_idx1) ←
          sign_loop4 { start := 0#usize, «end» := k }
            selections p.a leaf_idx node_idx
        let a3 := Array.repeat N 0#u8
        let leaves := Array.repeat 70#usize a3
        let a4 := Array.repeat N 0#u8
        let lvl1 := Array.repeat 35#usize a4
        let i3 ← 2#usize * k
        let s3 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) leaf_idx1
            { «end» := i3 }
        let (s4, index_mut_back1) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            leaves { «end» := i3 }
        let s5 ← ForsWideRows.leaves sk seed addr s3 s4
        let s6 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) node_idx1
            { «end» := k }
        let leaves1 := index_mut_back1 s5
        let s7 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            leaves1 { «end» := i3 }
        let (s8, index_mut_back2) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            lvl1 { «end» := k }
        let s9 ←
          ForsWideRows.pairs seed tree_adrs 1#u32 s6 s7 s8
        let lvl11 := index_mut_back2 s9
        let sig3 ←
          sign_loop5 { start := 0#usize, «end» := k } stride
            sig2 lvl11
        if p.a > 2#u32
        then
          let leaf_idx2 := Array.repeat 140#usize 0#u32
          let n1_idx := Array.repeat 70#usize 0#u32
          let n2_idx := Array.repeat 35#usize 0#u32
          let (leaf_idx3, n1_idx1, n2_idx1) ←
            sign_loop6 { start := 0#usize, «end» := k }
              selections p.a leaf_idx2 n1_idx n2_idx
          let a5 := Array.repeat N 0#u8
          let leaves2 := Array.repeat 140#usize a5
          let a6 := Array.repeat N 0#u8
          let lvl12 := Array.repeat 70#usize a6
          let a7 := Array.repeat N 0#u8
          let lvl2 := Array.repeat 35#usize a7
          let i4 ← 4#usize * k
          let s10 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) leaf_idx3
              { «end» := i4 }
          let (s11, index_mut_back3) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves2 { «end» := i4 }
          let s12 ← ForsWideRows.leaves sk seed addr s10 s11
          let i5 ← 2#usize * k
          let s13 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n1_idx1
              { «end» := i5 }
          let leaves3 := index_mut_back3 s12
          let s14 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves3 { «end» := i4 }
          let (s15, index_mut_back4) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl12 { «end» := i5 }
          let s16 ←
            ForsWideRows.pairs seed tree_adrs 1#u32 s13 s14 s15
          let s17 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n2_idx1
              { «end» := k }
          let lvl13 := index_mut_back4 s16
          let s18 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl13 { «end» := i5 }
          let (s19, index_mut_back5) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl2 { «end» := k }
          let s20 ←
            ForsWideRows.pairs seed tree_adrs 2#u32 s17 s18 s19
          let lvl21 := index_mut_back5 s20
          let sig4 ←
            sign_loop7 { start := 0#usize, «end» := k }
              stride sig3 lvl21
          sign_loop8 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig4
        else
          sign_loop9 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig3
      else
        if p.a > 2#u32
        then
          let leaf_idx := Array.repeat 140#usize 0#u32
          let n1_idx := Array.repeat 70#usize 0#u32
          let n2_idx := Array.repeat 35#usize 0#u32
          let (leaf_idx1, n1_idx1, n2_idx1) ←
            sign_loop10 { start := 0#usize, «end» := k }
              selections p.a leaf_idx n1_idx n2_idx
          let a3 := Array.repeat N 0#u8
          let leaves := Array.repeat 140#usize a3
          let a4 := Array.repeat N 0#u8
          let lvl1 := Array.repeat 70#usize a4
          let a5 := Array.repeat N 0#u8
          let lvl2 := Array.repeat 35#usize a5
          let i3 ← 4#usize * k
          let s3 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) leaf_idx1
              { «end» := i3 }
          let (s4, index_mut_back1) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves { «end» := i3 }
          let s5 ← ForsWideRows.leaves sk seed addr s3 s4
          let i4 ← 2#usize * k
          let s6 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n1_idx1
              { «end» := i4 }
          let leaves1 := index_mut_back1 s5
          let s7 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves1 { «end» := i3 }
          let (s8, index_mut_back2) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl1 { «end» := i4 }
          let s9 ←
            ForsWideRows.pairs seed tree_adrs 1#u32 s6 s7 s8
          let s10 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n2_idx1
              { «end» := k }
          let lvl11 := index_mut_back2 s9
          let s11 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl11 { «end» := i4 }
          let (s12, index_mut_back3) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl2 { «end» := k }
          let s13 ←
            ForsWideRows.pairs seed tree_adrs 2#u32 s10 s11 s12
          let lvl21 := index_mut_back3 s13
          let sig3 ←
            sign_loop11 { start := 0#usize, «end» := k }
              stride sig2 lvl21
          sign_loop12 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig3
        else
          sign_loop13 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig2
    else
      if p.a > 1#u32
      then
        let leaf_idx := Array.repeat 70#usize 0#u32
        let node_idx := Array.repeat 35#usize 0#u32
        let (leaf_idx1, node_idx1) ←
          sign_loop14 { start := 0#usize, «end» := k }
            selections p.a leaf_idx node_idx
        let a2 := Array.repeat N 0#u8
        let leaves := Array.repeat 70#usize a2
        let a3 := Array.repeat N 0#u8
        let lvl1 := Array.repeat 35#usize a3
        let i3 ← 2#usize * k
        let s ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) leaf_idx1
            { «end» := i3 }
        let (s1, index_mut_back) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            leaves { «end» := i3 }
        let s2 ← ForsWideRows.leaves sk seed addr s s1
        let s3 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) node_idx1
            { «end» := k }
        let leaves1 := index_mut_back s2
        let s4 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            leaves1 { «end» := i3 }
        let (s5, index_mut_back1) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
            lvl1 { «end» := k }
        let s6 ←
          ForsWideRows.pairs seed tree_adrs 1#u32 s3 s4 s5
        let lvl11 := index_mut_back1 s6
        let sig2 ←
          sign_loop15 { start := 0#usize, «end» := k }
            stride sig1 lvl11
        if p.a > 2#u32
        then
          let leaf_idx2 := Array.repeat 140#usize 0#u32
          let n1_idx := Array.repeat 70#usize 0#u32
          let n2_idx := Array.repeat 35#usize 0#u32
          let (leaf_idx3, n1_idx1, n2_idx1) ←
            sign_loop16 { start := 0#usize, «end» := k }
              selections p.a leaf_idx2 n1_idx n2_idx
          let a4 := Array.repeat N 0#u8
          let leaves2 := Array.repeat 140#usize a4
          let a5 := Array.repeat N 0#u8
          let lvl12 := Array.repeat 70#usize a5
          let a6 := Array.repeat N 0#u8
          let lvl2 := Array.repeat 35#usize a6
          let i4 ← 4#usize * k
          let s7 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) leaf_idx3
              { «end» := i4 }
          let (s8, index_mut_back2) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves2 { «end» := i4 }
          let s9 ← ForsWideRows.leaves sk seed addr s7 s8
          let i5 ← 2#usize * k
          let s10 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n1_idx1
              { «end» := i5 }
          let leaves3 := index_mut_back2 s9
          let s11 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves3 { «end» := i4 }
          let (s12, index_mut_back3) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl12 { «end» := i5 }
          let s13 ←
            ForsWideRows.pairs seed tree_adrs 1#u32 s10 s11 s12
          let s14 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n2_idx1
              { «end» := k }
          let lvl13 := index_mut_back3 s13
          let s15 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl13 { «end» := i5 }
          let (s16, index_mut_back4) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl2 { «end» := k }
          let s17 ←
            ForsWideRows.pairs seed tree_adrs 2#u32 s14 s15 s16
          let lvl21 := index_mut_back4 s17
          let sig3 ←
            sign_loop17 { start := 0#usize, «end» := k }
              stride sig2 lvl21
          sign_loop18 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig3
        else
          sign_loop19 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig2
      else
        if p.a > 2#u32
        then
          let leaf_idx := Array.repeat 140#usize 0#u32
          let n1_idx := Array.repeat 70#usize 0#u32
          let n2_idx := Array.repeat 35#usize 0#u32
          let (leaf_idx1, n1_idx1, n2_idx1) ←
            sign_loop20 { start := 0#usize, «end» := k }
              selections p.a leaf_idx n1_idx n2_idx
          let a2 := Array.repeat N 0#u8
          let leaves := Array.repeat 140#usize a2
          let a3 := Array.repeat N 0#u8
          let lvl1 := Array.repeat 70#usize a3
          let a4 := Array.repeat N 0#u8
          let lvl2 := Array.repeat 35#usize a4
          let i3 ← 4#usize * k
          let s ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) leaf_idx1
              { «end» := i3 }
          let (s1, index_mut_back) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves { «end» := i3 }
          let s2 ← ForsWideRows.leaves sk seed addr s s1
          let i4 ← 2#usize * k
          let s3 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n1_idx1
              { «end» := i4 }
          let leaves1 := index_mut_back s2
          let s4 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              leaves1 { «end» := i3 }
          let (s5, index_mut_back1) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl1 { «end» := i4 }
          let s6 ←
            ForsWideRows.pairs seed tree_adrs 1#u32 s3 s4 s5
          let s7 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) n2_idx1
              { «end» := k }
          let lvl11 := index_mut_back1 s6
          let s8 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl11 { «end» := i4 }
          let (s9, index_mut_back2) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
              lvl2 { «end» := k }
          let s10 ←
            ForsWideRows.pairs seed tree_adrs 2#u32 s7 s8 s9
          let lvl21 := index_mut_back2 s10
          let sig2 ←
            sign_loop21 { start := 0#usize, «end» := k }
              stride sig1 lvl21
          sign_loop22 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig2
        else
          sign_loop23 { start := 0#usize, «end» := k }
            selections sk seed addr.layer addr.tree addr.typ addr.keypair
            addr.word2 addr.word3 p.a stride sig1
end slhdsa.ForsDriver
