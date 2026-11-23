import Shakebatch.WotsChainProgram
import Shakebatch.RecoverProgram
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine] [stream : Stream]

@[reducible]
def shake.batch.keygen.closure (N : Std.Usize) := Std.Usize

def
  shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  {N : Std.Usize} (c : shake.batch.keygen.closure N) (tupled_args : Std.Usize)
  :
  Result (Std.Usize × (shake.batch.keygen.closure N))
  := do
  let i ← c + tupled_args
  ok (i, c)

def
  shake.batch.keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
  {N : Std.Usize} (c : shake.batch.keygen.closure N) (i : Std.Usize) :
  Result Std.Usize
  := do
  let (i1, _) ←
    shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
      c i
  ok i1

@[reducible]
def shake.batch.keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.keygen.closure N)
  Std.Usize Std.Usize := {
  call_once :=
    shake.batch.keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
}

@[reducible]
def shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.keygen.closure N) Std.Usize
  Std.Usize := {
  FnOnceInst :=
    shake.batch.keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize N
  call_mut :=
    shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
}

@[rust_loop_body]
def shake.batch.keygen_loop0_loop0.body
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result (ControlFlow ((core.slice.iter.Iter (Array Std.U8 N)) ×
    stream.State) stream.State)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done pk)
  | some v =>
    let s ← lift (Array.to_slice v)
    let pk1 ← stream.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def shake.batch.keygen_loop0_loop0
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => shake.batch.keygen_loop0_loop0.body iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def shake.batch.keygen_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (len : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (pk : stream.State) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × stream.State) stream.State)
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done pk)
  | some i6 =>
    let ids ←
      core.array.from_fn machine.width
        (shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize
        N) i6
    let values ←
      shake.batch.secrets seed sk
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } ids
    let a := Array.repeat machine.width 0#u32
    let i7 ← params.W - 1#u32
    let a1 := Array.repeat machine.width i7
    let values1 ←
      shake.batch.chains seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } ids values a a1
    let i8 ← len - i6
    let i9 ← lift (core.cmp.impls.OrdUsize.min i8 machine.width)
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
        values1 { «end» := i9 }
    let iter2 ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    let pk1 ← shake.batch.keygen_loop0_loop0 iter2 pk
    ok (cont (iter1, pk1))

@[rust_loop]
def shake.batch.keygen_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64)
  (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (len : Std.Usize)
  (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => shake.batch.keygen_loop0.body sk seed i i1 i2 i3 i4 i5
      len iter1 pk1)
    (iter, pk)

def shake.batch.keygen
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← 2#usize * N
  let len ← i + params.LEN2
  let a ← address.Adrs.with_type addr address.WOTS_PK
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let pk ← stream.start seed a1
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := len } machine.width
  let pk1 ←
    shake.batch.keygen_loop0 iter sk seed addr.layer addr.tree addr.typ
      addr.keypair addr.word2 addr.word3 len pk
  stream.digest N pk1
end
end slhdsa.ShakeBatch
