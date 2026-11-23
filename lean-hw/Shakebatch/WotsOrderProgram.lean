import Slhdsa.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section


@[rust_loop_body]
def shake.batch.chain_order_loop0.body
  (iter : core.slice.iter.Iter Std.U32) (offsets : Array Std.Usize 16#usize) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (Array Std.Usize
    16#usize)) (Array Std.Usize 16#usize))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done offsets)
  | some digit =>
    let i ← lift (UScalar.cast .Usize digit)
    let i1 ← Array.index_usize offsets i
    let i2 ← i1 + 1#usize
    let a ← Array.update offsets i i2
    ok (cont (iter1, a))

@[rust_loop]
def shake.batch.chain_order_loop0
  (iter : core.slice.iter.Iter Std.U32) (offsets : Array Std.Usize 16#usize) :
  Result (Array Std.Usize 16#usize)
  := do
  loop
    (fun (iter1, offsets1) => shake.batch.chain_order_loop0.body iter1
      offsets1)
    (iter, offsets)

@[rust_loop_body]
def shake.batch.chain_order_loop1.body
  (iter : core.slice.iter.IterMut Std.Usize)
  (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut
  Std.Usize) (start : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.IterMut Std.Usize) ×
    (core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)
    × Std.Usize) ((core.slice.iter.IterMut Std.Usize) ×
    (core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut Std.Usize)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some offset =>
    let start1 ← start + offset
    ok (cont (iter1, fun im => let im1 := next_back im (some start)
                               back im1, start1))

@[rust_loop]
def shake.batch.chain_order_loop1
  (iter : core.slice.iter.IterMut Std.Usize)
  (back : core.slice.iter.IterMut Std.Usize → core.slice.iter.IterMut
  Std.Usize) (start : Std.Usize) :
  Result ((core.slice.iter.IterMut Std.Usize) × (core.slice.iter.IterMut
    Std.Usize → core.slice.iter.IterMut Std.Usize))
  := do
  loop
    (fun (iter1, back1, start1) => shake.batch.chain_order_loop1.body iter1
      back1 start1)
    (iter, back, start)

@[rust_loop_body]
def shake.batch.chain_order_loop2.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (offsets : Array Std.Usize 16#usize)
  (order : Array Std.Usize 67#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U32)) × (Array Std.Usize 16#usize) × (Array
    Std.Usize 67#usize)) (Array Std.Usize 67#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done order)
  | some p =>
    let (index, digit) := p
    let i ← lift (UScalar.cast .Usize digit)
    let («at», index_mut_back) ← Array.index_mut_usize offsets i
    let a ← Array.update order «at» index
    let at1 ← «at» + 1#usize
    let a1 := index_mut_back at1
    ok (cont (iter1, a1, a))

@[rust_loop]
def shake.batch.chain_order_loop2
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (offsets : Array Std.Usize 16#usize)
  (order : Array Std.Usize 67#usize) :
  Result (Array Std.Usize 67#usize)
  := do
  loop
    (fun (iter1, offsets1, order1) => shake.batch.chain_order_loop2.body iter1
      offsets1 order1)
    (iter, offsets, order)

def shake.batch.chain_order
  (digits : Slice Std.U32) : Result (Array Std.Usize 67#usize) := do
  let offsets := Array.repeat 16#usize 0#usize
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      digits
  let offsets1 ← shake.batch.chain_order_loop0 iter offsets
  let (iter1, into_iter_back) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
      offsets1
  let (im, back) ←
    shake.batch.chain_order_loop1 iter1 (fun im1 => im1) 0#usize
  let order := Array.repeat 67#usize 0#usize
  let i ← core.slice.Slice.iter digits
  let iter2 ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i
  let im1 := back im
  let a := into_iter_back im1
  shake.batch.chain_order_loop2 iter2 a order
end
end slhdsa.ShakeBatch
