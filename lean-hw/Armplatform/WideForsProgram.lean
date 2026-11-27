import Armwide.Encoders
import Slhdsa.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.WideFors

@[rust_loop_body]
def fors.arm.pk_from_sig_loop0.body
  (a : Std.U32) (raw : Array Std.U32 35#usize)
  (iter : core.ops.range.Range Std.Usize) (idx : Array Std.U32 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    35#usize)) (Array Std.U32 35#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done idx)
  | some i =>
    let i1 ← lift (UScalar.cast .U32 i)
    let i2 ← i1 <<< a
    let i3 ← Array.index_usize raw i
    let i4 ← i2 + i3
    let a1 ← Array.update idx i i4
    ok (cont (iter1, a1))

@[rust_loop]
def fors.arm.pk_from_sig_loop0
  (iter : core.ops.range.Range Std.Usize) (a : Std.U32)
  (raw : Array Std.U32 35#usize) (idx : Array Std.U32 35#usize) :
  Result (Array Std.U32 35#usize)
  := do
  loop
    (fun (iter1, idx1) => fors.arm.pk_from_sig_loop0.body a raw iter1 idx1)
    (iter, idx)


@[rust_loop_body]
def fors.arm.pk_from_sig_loop2.body
  (vals : Array (Array Std.U8 16#usize) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (buf : Array Std.U8 640#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8
    640#usize)) (Array Std.U8 640#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done buf)
  | some i =>
    let i1 ← 16#usize * i
    let i2 ← 22#usize + i1
    let i3 ← i + 1#usize
    let i4 ← 16#usize * i3
    let i5 ← 22#usize + i4
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) buf
        { start := i2, «end» := i5 }
    let a ← Array.index_usize vals i
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let buf1 := index_mut_back s2
    ok (cont (iter1, buf1))

@[rust_loop]
def fors.arm.pk_from_sig_loop2
  (iter : core.ops.range.Range Std.Usize)
  (vals : Array (Array Std.U8 16#usize) 35#usize)
  (buf : Array Std.U8 640#usize) :
  Result (Array Std.U8 640#usize)
  := do
  loop
    (fun (iter1, buf1) => fors.arm.pk_from_sig_loop2.body vals iter1 buf1)
    (iter, buf)

@[rust_loop_body]
def fors.arm.pk_from_sig_loop4.body
  {N : Std.Usize} (vals : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (buf : Array Std.U8 1280#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8
    1280#usize)) (Array Std.U8 1280#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done buf)
  | some i =>
    let i1 ← N * i
    let i2 ← 22#usize + i1
    let i3 ← i + 1#usize
    let i4 ← N * i3
    let i5 ← 22#usize + i4
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) buf
        { start := i2, «end» := i5 }
    let a ← Array.index_usize vals i
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let buf1 := index_mut_back s2
    ok (cont (iter1, buf1))

@[rust_loop]
def fors.arm.pk_from_sig_loop4
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (vals : Array (Array Std.U8 N) 35#usize) (buf : Array Std.U8 1280#usize) :
  Result (Array Std.U8 1280#usize)
  := do
  loop
    (fun (iter1, buf1) => fors.arm.pk_from_sig_loop4.body vals iter1 buf1)
    (iter, buf)

@[rust_loop_body]
def packRoots.body
  {N capacity : Std.Usize} (vals : Array (Array Std.U8 N) 35#usize)
  (iter : core.ops.range.Range Std.Usize) (buf : Array Std.U8 capacity) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8
    capacity)) (Array Std.U8 capacity))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done buf)
  | some i =>
    let i1 ← N * i
    let i2 ← 22#usize + i1
    let i3 ← i + 1#usize
    let i4 ← N * i3
    let i5 ← 22#usize + i4
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) buf
        { start := i2, «end» := i5 }
    let a ← Array.index_usize vals i
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let buf1 := index_mut_back s2
    ok (cont (iter1, buf1))

@[rust_loop]
def packRoots
  {N capacity : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (vals : Array (Array Std.U8 N) 35#usize) (buf : Array Std.U8 capacity) :
  Result (Array Std.U8 capacity)
  := do
  loop
    (fun (iter1, buf1) => packRoots.body vals iter1 buf1)
    (iter, buf)

@[rust_loop_body]
def fors.arm.pk_from_sig_loop5.body
  (buf : Array Std.U8 1280#usize) (total : Std.Usize)
  (st : Array Std.U64 8#usize) (off : Std.Usize) :
  Result (ControlFlow ((Array Std.U64 8#usize) × Std.Usize) (Array Std.U64
    8#usize))
  := do
  if off < total
  then
    let s ← lift (Array.to_slice buf)
    let st1 ← sha512.compress st s off
    let off1 ← off + 128#usize
    ok (cont (st1, off1))
  else ok (done st)

@[rust_loop]
def fors.arm.pk_from_sig_loop5
  (buf : Array Std.U8 1280#usize) (total : Std.Usize)
  (st : Array Std.U64 8#usize) (off : Std.Usize) :
  Result (Array Std.U64 8#usize)
  := do
  loop
    (fun (st1, off1) => fors.arm.pk_from_sig_loop5.body buf total st1 off1)
    (st, off)

@[rust_loop_body]
def fors.arm.pk_from_sig_loop3_loop0.body
  {N : Std.Usize} (sig : Slice Std.U8) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize) (a3 : Std.U32)
  (h : Std.Usize) (adr : address.Adrs) (iter : core.ops.range.Range Std.Usize)
  (idx : Array Std.U32 35#usize) (vals : Array (Array Std.U8 N) 35#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    35#usize) × (Array (Array Std.U8 N) 35#usize)) ((Array Std.U32 35#usize)
    × (Array (Array Std.U8 N) 35#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (idx, vals))
  | some i =>
    let i1 ← lift (UScalar.cast .Usize a3)
    let i2 ← i1 + 1#usize
    let i3 ← i * i2
    let i4 ← i3 + 1#usize
    let i5 ← i4 + h
    let sibling ← util.block N sig i5
    let i6 ← Array.index_usize idx i
    let parent ← i6 >>> 1#i32
    let a_node ← address.Adrs.with_word3 adr parent
    let i7 ← lift (i6 &&& 1#u32)
    let vals1 ←
      if i7 = 0#u32
      then
        do
        let a4 ← Array.index_usize vals i
        let a5 ←
          hash.thash_pair { pk_seed := a, state := a1, state512 := a2 } a_node
            a4 sibling
        Array.update vals i a5
      else
        do
        let a4 ← Array.index_usize vals i
        let a5 ←
          hash.thash_pair { pk_seed := a, state := a1, state512 := a2 } a_node
            sibling a4
        Array.update vals i a5
    let a4 ← Array.update idx i parent
    ok (cont (iter1, a4, vals1))

@[rust_loop]
def fors.arm.pk_from_sig_loop3_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (sig : Slice Std.U8)
  (a : Array Std.U8 N) (a1 : Array Std.U32 8#usize)
  (a2 : Array Std.U64 8#usize) (a3 : Std.U32) (idx : Array Std.U32 35#usize)
  (vals : Array (Array Std.U8 N) 35#usize) (h : Std.Usize) (adr : address.Adrs)
  :
  Result ((Array Std.U32 35#usize) × (Array (Array Std.U8 N) 35#usize))
  := do
  loop
    (fun (iter1, idx1, vals1) => fors.arm.pk_from_sig_loop3_loop0.body sig a a1
      a2 a3 h adr iter1 idx1 vals1)
    (iter, idx, vals)

end slhdsa.WideFors
