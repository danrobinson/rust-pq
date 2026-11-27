import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Armwide.SignOrder

@[rust_loop_body]
def sha256.arm_wide.sign_order_loop0.body
  (iter : core.slice.iter.Iter Std.U32) (counts : Array Std.U8 16#usize) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (Array Std.U8
    16#usize)) (Array Std.U8 16#usize))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done counts)
  | some d =>
    let i ← lift (UScalar.cast .Usize d)
    let i1 ← Array.index_usize counts i
    let i2 ← i1 + 1#u8
    let a ← Array.update counts i i2
    ok (cont (iter1, a))

@[rust_loop]
def sha256.arm_wide.sign_order_loop0
  (iter : core.slice.iter.Iter Std.U32) (counts : Array Std.U8 16#usize) :
  Result (Array Std.U8 16#usize)
  := do
  loop
    (fun (iter1, counts1) => sha256.arm_wide.sign_order_loop0.body iter1
      counts1)
    (iter, counts)

@[rust_loop_body]
def sha256.arm_wide.sign_order_loop1.body
  (counts : Array Std.U8 16#usize) (offsets : Array Std.Usize 16#usize)
  (total : Std.Usize) (b : Std.Isize) :
  Result (ControlFlow ((Array Std.Usize 16#usize) × Std.Usize × Std.Isize)
    (Array Std.Usize 16#usize))
  := do
  if b >= 0#isize
  then
    let i ← lift (IScalar.hcast .Usize b)
    let a ← Array.update offsets i total
    let i1 ← lift (IScalar.hcast .Usize b)
    let i2 ← Array.index_usize counts i1
    let i3 ← lift (UScalar.cast .Usize i2)
    let total1 ← total + i3
    let b1 ← b - 1#isize
    ok (cont (a, total1, b1))
  else ok (done offsets)

@[rust_loop]
def sha256.arm_wide.sign_order_loop1
  (counts : Array Std.U8 16#usize) (offsets : Array Std.Usize 16#usize)
  (total : Std.Usize) (b : Std.Isize) :
  Result (Array Std.Usize 16#usize)
  := do
  loop
    (fun (offsets1, total1, b1) => sha256.arm_wide.sign_order_loop1.body counts
      offsets1 total1 b1)
    (offsets, total, b)

@[rust_loop_body]
def sha256.arm_wide.sign_order_loop2.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (offsets : Array Std.Usize 16#usize)
  (order : Array Std.U8 67#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U32)) × (Array Std.Usize 16#usize) × (Array
    Std.U8 67#usize)) (Array Std.U8 67#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done order)
  | some p =>
    let (i, d) := p
    let i1 ← lift (UScalar.cast .Usize d)
    let pos ← Array.index_usize offsets i1
    let i2 ← lift (UScalar.cast .U8 i)
    let a ← Array.update order pos i2
    let i3 ← pos + 1#usize
    let i4 ← lift (UScalar.cast .Usize d)
    let a1 ← Array.update offsets i4 i3
    ok (cont (iter1, a1, a))

@[rust_loop]
def sha256.arm_wide.sign_order_loop2
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (offsets : Array Std.Usize 16#usize)
  (order : Array Std.U8 67#usize) :
  Result (Array Std.U8 67#usize)
  := do
  loop
    (fun (iter1, offsets1, order1) => sha256.arm_wide.sign_order_loop2.body
      iter1 offsets1 order1)
    (iter, offsets, order)

def sha256.arm_wide.sign_order
  (digits : Slice Std.U32) : Result (Array Std.U8 67#usize) := do
  let counts := Array.repeat 16#usize 0#u8
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      digits
  let counts1 ← sha256.arm_wide.sign_order_loop0 iter counts
  let offsets := Array.repeat 16#usize 0#usize
  let offsets1 ←
    sha256.arm_wide.sign_order_loop1 counts1 offsets 0#usize 15#isize
  let order := Array.repeat 67#usize 0#u8
  let i ← core.slice.Slice.iter digits
  let iter1 ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i
  sha256.arm_wide.sign_order_loop2 iter1 offsets1 order

end slhdsa.Armwide.SignOrder
