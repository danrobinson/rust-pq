import Shakebatch.WriteRows
import Shakebatch.Selection
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsSign
variable [machine : ShakeBatch.Machine]
variable (short : {N : Std.Usize} → Array Std.U8 N → Array address.Adrs machine.width → ShakeBatch.Rows N → Std.Usize → Result (ShakeBatch.Rows N))
def sign.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize × address.Adrs × Std.U32 × Slice Std.U32

def
  sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
  {N : Std.Usize} (c : sign.closure N)
  (tupled_args : Std.Usize) :
  Result (address.Adrs × (sign.closure N))
  := do
  let (i, i1, a, i2, s) := c
  let i3 ← i1 - 1#usize
  let i4 ← lift (core.cmp.impls.OrdUsize.min tupled_args i3)
  let tree ← i + i4
  let i5 ← lift (UScalar.cast .U32 tree)
  let i6 ← i5 <<< i2
  let i7 ← Slice.index_usize s tree
  let i8 ← i6 + i7
  let a1 ← address.Adrs.with_word3 a i8
  ok (a1, c)

def
  sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
  {N : Std.Usize} (c : sign.closure N) (i : Std.Usize) :
  Result address.Adrs
  := do
  let (a, _) ←
    sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
      c i
  ok a

@[reducible]
def sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs (N
  : Std.Usize) : core.ops.function.FnOnce (sign.closure N)
  Std.Usize address.Adrs := {
  call_once :=
    sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
}

@[reducible]
def sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs (N :
  Std.Usize) : core.ops.function.FnMut (sign.closure N)
  Std.Usize address.Adrs := {
  FnOnceInst :=
    sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs N
  call_mut :=
    sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
}

@[rust_loop_body]
def sign_loop0_loop0.body
  {N : Std.Usize} (stride : Std.Usize) (first : Std.Usize)
  (sec : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some lane =>
    let i ← first + lane
    let i1 ← i * stride
    let i2 ← i * stride
    let i3 ← i2 + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i1, «end» := i3 }
    let a ← Array.index_usize sec lane
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))

@[rust_loop]
def sign_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (first : Std.Usize)
  (sec : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop0_loop0.body stride first
      sec iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def sign_loop0.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (k : Std.Usize) (a : Std.U32) (stride : Std.Usize)
  (prf : address.Adrs) (sig : alloc.vec.Vec Std.U8) (first : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.Usize) (alloc.vec.Vec
    Std.U8))
  := do
  if first < k
  then
    let i ← k - first
    let active ← lift (core.cmp.impls.OrdUsize.min i machine.width)
    let addrs ←
      core.array.from_fn machine.width
        (sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs
        N) (first, active, prf, a, selections)
    let a1 := Array.repeat machine.width sk
    let sec ← short seed addrs a1 active
    let sig1 ←
      sign_loop0_loop0 { start := 0#usize, «end» := active }
        stride sig first sec
    let first1 ← first + active
    ok (cont (sig1, first1))
  else ok (done sig)

@[rust_loop]
def sign_loop0
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (k : Std.Usize) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (prf : address.Adrs) (first : Std.Usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, first1) => sign_loop0.body short selections sk seed
      k a stride prf sig1 first1)
    (sig, first)

@[rust_loop_body]
def sign_loop1_loop0_loop0.body
  {N : Std.Usize} (stride : Std.Usize) (first : Std.Usize) (j : Std.U32)
  (siblings : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some lane =>
    let i ← first + lane
    let i1 ← i * stride
    let i2 ← lift (UScalar.cast .Usize j)
    let i3 ← i2 + 1#usize
    let i4 ← i3 * N
    let pos ← i1 + i4
    let i5 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i5 }
    let a ← Array.index_usize siblings lane
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))

@[rust_loop]
def sign_loop1_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (first : Std.Usize) (j : Std.U32)
  (siblings : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop1_loop0_loop0.body stride
      first j siblings iter1 sig1)
    (iter, sig)
end slhdsa.NativeVerify.ForsSign
