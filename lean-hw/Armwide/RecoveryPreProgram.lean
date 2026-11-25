import Armwide.Funs
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Armwide.Recovery



@[rust_loop_body]
def prepare_loop.body
  (N : Std.Usize) (digits : Slice Std.U32) (sig : Slice Std.U8)
  (iter : core.ops.range.Range Std.Usize) (buf : Slice Std.U8)
  (rem_weights : Array Std.U32 67#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U8) ×
    (Array Std.U32 67#usize)) ((Array Std.U32 67#usize) × (Slice Std.U8)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (rem_weights, buf))
  | some i =>
    let d ← Slice.index_usize digits i
    if d = 15#u32
    then
      let i1 ← i * N
      let i2 ← 22#usize + i1
      let i3 ← i + 1#usize
      let i4 ← i3 * N
      let i5 ← 22#usize + i4
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) buf
          { start := i2, «end» := i5 }
      let i6 ← i3 * N
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sig
          { start := i1, «end» := i6 }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let buf1 := index_mut_back s2
      ok (cont (iter1, buf1, rem_weights))
    else
      let i1 ← 15#u32 - d
      let a ← Array.update rem_weights i i1
      ok (cont (iter1, buf, a))


@[rust_loop]
def prepare_loop
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (digits : Slice Std.U32) (sig : Slice Std.U8) (buf : Slice Std.U8)
  (rem_weights : Array Std.U32 67#usize) :
  Result ((Array Std.U32 67#usize) × (Slice Std.U8))
  := do
  loop
    (fun (iter1, buf1, rem_weights1) =>
      prepare_loop.body N digits sig iter1 buf1
      rem_weights1)
    (iter, buf, rem_weights)


def prepare
  (N : Std.Usize) (digits : Slice Std.U32) (sig : Slice Std.U8)
  (buf : Slice Std.U8) :
  Result ((Array Std.U32 67#usize) × (Slice Std.U8))
  := do
  let len := Slice.len digits
  let rem_weights := Array.repeat 67#usize 0#u32
  prepare_loop N { start := 0#usize, «end» := len }
    digits sig buf rem_weights

end slhdsa.Armwide.Recovery
