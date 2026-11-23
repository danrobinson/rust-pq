import Shakebatch.WotsChainProgram
import Shakebatch.WotsOrderProgram
import Shakebatch.WotsChunks
import Shakebatch.RecoverProgram
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine] [stream : Stream]

@[reducible]
def shake.batch.sign.closure_1 (N : Std.Usize) := Slice Std.U32

@[reducible]
def shake.batch.sign.closure (N : Std.Usize) := Slice Std.Usize

@[reducible]
def shake.batch.recover.closure_2 (N : Std.Usize) := Slice Std.U32

@[reducible]
def shake.batch.recover.closure_1 (N : Std.Usize) := Slice Std.U8

@[reducible]
def shake.batch.recover.closure (N : Std.Usize) := Slice Std.Usize

def shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : shake.batch.sign.closure_1 N) (tupled_args : Std.Usize)
  :
  Result (Std.U32 × (shake.batch.sign.closure_1 N))
  := do
  let i ← Slice.index_usize c tupled_args
  ok (i, c)

def
  shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : shake.batch.sign.closure_1 N) (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.sign.closure_1 N)
  Std.Usize Std.U32 := {
  call_once :=
    shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.sign.closure_1 N) Std.Usize
  Std.U32 := {
  FnOnceInst :=
    shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 N
  call_mut :=
    shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

def shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  {N : Std.Usize} (c : shake.batch.sign.closure N) (tupled_args : Std.Usize) :
  Result (Std.Usize × (shake.batch.sign.closure N))
  := do
  let i := Slice.len c
  let i1 ← i - 1#usize
  let i2 ← lift (core.cmp.impls.OrdUsize.min tupled_args i1)
  let i3 ← Slice.index_usize c i2
  ok (i3, c)

def
  shake.batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
  {N : Std.Usize} (c : shake.batch.sign.closure N) (i : Std.Usize) :
  Result Std.Usize
  := do
  let (i1, _) ←
    shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
      c i
  ok i1

@[reducible]
def shake.batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.sign.closure N) Std.Usize
  Std.Usize := {
  call_once :=
    shake.batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
}

@[reducible]
def shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.sign.closure N) Std.Usize
  Std.Usize := {
  FnOnceInst :=
    shake.batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize N
  call_mut :=
    shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
}

@[rust_loop_body]
def shake.batch.sign_loop0_loop0.body
  {N : Std.Usize} (values : Array (Array Std.U8 N) machine.width)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.Usize)) × (alloc.vec.Vec Std.U8)) (alloc.vec.Vec
    Std.U8))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) iter
  match o with
  | none => ok (done sig)
  | some p =>
    let (lane, id) := p
    let i ← id * N
    let i1 ← id + 1#usize
    let i2 ← i1 * N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i, «end» := i2 }
    let a ← Array.index_usize values lane
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))

@[rust_loop]
def shake.batch.sign_loop0_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (sig : alloc.vec.Vec Std.U8)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.batch.sign_loop0_loop0.body values iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def shake.batch.sign_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (digits : Slice Std.U32)
  (iter : core.slice.iter.Chunks Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done sig)
  | some batch =>
    let ids ←
      core.array.from_fn machine.width
        (shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N)
        batch
    let values ← shake.batch.secrets seed sk addr ids
    let a := Array.repeat machine.width 0#u32
    let a1 ←
      core.array.Array.map
        (shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
        ids digits
    let values1 ← shake.batch.chains seed addr ids values a a1
    let i ← core.slice.Slice.iter batch
    let iter2 ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.Usize) i
    let sig1 ← shake.batch.sign_loop0_loop0 iter2 sig values1
    ok (cont (iter1, sig1))

@[rust_loop]
def shake.batch.sign_loop0
  {N : Std.Usize} (iter : core.slice.iter.Chunks Std.Usize)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs)
  (digits : Slice Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.batch.sign_loop0.body sk seed addr digits iter1
      sig1)
    (iter, sig)

def shake.batch.sign
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (digits : Slice Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let order ← shake.batch.chain_order digits
  let i := Slice.len digits
  let i1 ← N * i
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i1
  let i2 := Slice.len digits
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.Usize)) order
      { «end» := i2 }
  let iter ← core.slice.Slice.chunks s machine.width
  shake.batch.sign_loop0 iter sk seed addr digits sig

def
  shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : shake.batch.recover.closure_2 N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (shake.batch.recover.closure_2 N))
  := do
  let i ← Slice.index_usize c tupled_args
  ok (i, c)

def
  shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : shake.batch.recover.closure_2 N) (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.recover.closure_2 N)
  Std.Usize Std.U32 := {
  call_once :=
    shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32 (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.recover.closure_2 N)
  Std.Usize Std.U32 := {
  FnOnceInst :=
    shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 N
  call_mut :=
    shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

def
  shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : shake.batch.recover.closure_1 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (shake.batch.recover.closure_1 N))
  := do
  let a ← util.block N c tupled_args
  ok (a, c)

def
  shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : shake.batch.recover.closure_1 N) (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce (shake.batch.recover.closure_1 N)
  Std.Usize (Array Std.U8 N) := {
  call_once :=
    shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut (shake.batch.recover.closure_1 N)
  Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  {N : Std.Usize} (c : shake.batch.recover.closure N) (tupled_args : Std.Usize)
  :
  Result (Std.Usize × (shake.batch.recover.closure N))
  := do
  let i := Slice.len c
  let i1 ← i - 1#usize
  let i2 ← lift (core.cmp.impls.OrdUsize.min tupled_args i1)
  let i3 ← Slice.index_usize c i2
  ok (i3, c)

def
  shake.batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
  {N : Std.Usize} (c : shake.batch.recover.closure N) (i : Std.Usize) :
  Result Std.Usize
  := do
  let (i1, _) ←
    shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
      c i
  ok i1

@[reducible]
def shake.batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.recover.closure N)
  Std.Usize Std.Usize := {
  call_once :=
    shake.batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
}

@[reducible]
def shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.recover.closure N)
  Std.Usize Std.Usize := {
  FnOnceInst :=
    shake.batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize N
  call_mut :=
    shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
}

@[rust_loop_body]
def shake.batch.recover_loop0_loop0.body
  {N : Std.Usize} (values : Array (Array Std.U8 N) machine.width)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (endpoints : Array (Array Std.U8 N) 67#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.Usize)) × (Array (Array Std.U8 N) 67#usize))
    (Array (Array Std.U8 N) 67#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) iter
  match o with
  | none => ok (done endpoints)
  | some p =>
    let (lane, id) := p
    let a ← Array.index_usize values lane
    let a1 ← Array.update endpoints id a
    ok (cont (iter1, a1))

@[rust_loop]
def shake.batch.recover_loop0_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (endpoints : Array (Array Std.U8 N) 67#usize)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) 67#usize)
  := do
  loop
    (fun (iter1, endpoints1) => shake.batch.recover_loop0_loop0.body values
      iter1 endpoints1)
    (iter, endpoints)

@[rust_loop_body]
def shake.batch.recover_loop0.body
  {N : Std.Usize} (sig : Slice Std.U8) (seed : Array Std.U8 N)
  (addr : address.Adrs) (digits : Slice Std.U32)
  (iter : core.slice.iter.Chunks Std.Usize)
  (endpoints : Array (Array Std.U8 N) 67#usize) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.Usize) × (Array (Array
    Std.U8 N) 67#usize)) (Array (Array Std.U8 N) 67#usize))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done endpoints)
  | some batch =>
    let ids ←
      core.array.from_fn machine.width
        (shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize
        N) batch
    let values ←
      core.array.Array.map
        (shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) ids sig
    let a ←
      core.array.Array.map
        (shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        N) ids digits
    let i ← params.W - 1#u32
    let a1 := Array.repeat machine.width i
    let values1 ← shake.batch.chains seed addr ids values a a1
    let i1 ← core.slice.Slice.iter batch
    let iter2 ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.Usize) i1
    let endpoints1 ← shake.batch.recover_loop0_loop0 iter2 endpoints values1
    ok (cont (iter1, endpoints1))

@[rust_loop]
def shake.batch.recover_loop0
  {N : Std.Usize} (iter : core.slice.iter.Chunks Std.Usize)
  (sig : Slice Std.U8) (seed : Array Std.U8 N) (addr : address.Adrs)
  (digits : Slice Std.U32) (endpoints : Array (Array Std.U8 N) 67#usize) :
  Result (Array (Array Std.U8 N) 67#usize)
  := do
  loop
    (fun (iter1, endpoints1) => shake.batch.recover_loop0.body sig seed addr
      digits iter1 endpoints1)
    (iter, endpoints)

@[rust_loop_body]
def shake.batch.recover_loop1.body
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result (ControlFlow ((core.slice.iter.Iter (Array Std.U8 N)) ×
    stream.State) stream.State)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done pk)
  | some key =>
    let s ← lift (Array.to_slice key)
    let pk1 ← stream.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def shake.batch.recover_loop1
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => shake.batch.recover_loop1.body iter1 pk1)
    (iter, pk)

def shake.batch.recover
  {N : Std.Usize} (sig : Slice Std.U8) (seed : Array Std.U8 N)
  (addr : address.Adrs) (digits : Slice Std.U32) :
  Result (Array Std.U8 N)
  := do
  let order ← shake.batch.chain_order digits
  let a := Array.repeat N 0#u8
  let endpoints := Array.repeat 67#usize a
  let i := Slice.len digits
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.Usize)) order
      { «end» := i }
  let iter ← core.slice.Slice.chunks s machine.width
  let endpoints1 ←
    shake.batch.recover_loop0 iter sig seed addr digits endpoints
  let a1 ← address.Adrs.with_type addr address.WOTS_PK
  let a2 ← address.Adrs.with_keypair a1 addr.keypair
  let pk ← stream.start seed a2
  let i1 := Slice.len digits
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
      endpoints1 { «end» := i1 }
  let iter1 ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s1
  let pk1 ← shake.batch.recover_loop1 iter1 pk
  stream.digest N pk1
end
end slhdsa.ShakeBatch
