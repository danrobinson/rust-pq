import Shakebatch.NodesProgram
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
class Stream where
  State : Type
  start {N : Usize} : Array U8 N → address.Adrs → Result State
  absorb : State → Slice U8 → Result State
  digest (N : Usize) : State → Result (Array U8 N)
variable [machine : Machine] [stream : Stream]

def shake.fors_batch.recover.closure_8 (N : Std.Usize) :=
  address.Adrs × Std.U32

@[reducible]
def shake.fors_batch.recover.closure_7 (N : Std.Usize) := Unit

def shake.fors_batch.recover.closure_6 (N : Std.Usize) :=
  Array Std.U32 machine.width × Array (Array Std.U8 N) machine.width × Array (Array
  Std.U8 N) machine.width

def shake.fors_batch.recover.closure_5 (N : Std.Usize) :=
  Array Std.U32 machine.width × Array (Array Std.U8 N) machine.width × Array (Array
  Std.U8 N) machine.width

def shake.fors_batch.recover.closure_4 (N : Std.Usize) :=
  Slice Std.U8 × Std.Usize × Std.U32

@[reducible]
def shake.fors_batch.recover.closure_3 (N : Std.Usize) := address.Adrs

def shake.fors_batch.recover.closure_2 (N : Std.Usize) :=
  Slice Std.U8 × Std.Usize

def shake.fors_batch.recover.closure_1 (N : Std.Usize) :=
  params.Params × Slice Std.U32

def shake.fors_batch.recover.closure (N : Std.Usize) := Std.Usize × Std.Usize

def
  shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_8 N)
  (tupled_args : Std.U32) :
  Result (address.Adrs × (shake.fors_batch.recover.closure_8 N))
  := do
  let (a, i) := c
  let i1 ← i + 1#u32
  let a1 ← address.Adrs.with_word2 a i1
  let a2 ← address.Adrs.with_word3 a1 tupled_args
  ok (a2, c)

def
  shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_8 N) (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_8 N) Std.U32 address.Adrs := {
  call_once :=
    shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_8
  N) Std.U32 address.Adrs := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
    N
  call_mut :=
    shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def
  shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_7 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (shake.fors_batch.recover.closure_7 N))
  := do
  let i ← tupled_args >>> 1#i32
  ok (i, c)

def
  shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_7 N) (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnOnceTupleU32U32
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_7 N) Std.U32 Std.U32 := {
  call_once :=
    shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32 (N
  : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_7 N)
  Std.U32 Std.U32 := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnOnceTupleU32U32 N
  call_mut :=
    shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_6 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (shake.fors_batch.recover.closure_6 N))
  := do
  let (a, a1, a2) := c
  let i ← Array.index_usize a tupled_args
  let i1 ← lift (i &&& 1#u32)
  if i1 = 0#u32
  then let a3 ← Array.index_usize a1 tupled_args
       ok (a3, c)
  else let a3 ← Array.index_usize a2 tupled_args
       ok (a3, c)

def
  shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_6 N) (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def
  shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_6 N) Std.Usize (Array Std.U8 N) := {
  call_once :=
    shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def
  shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_6
  N) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_5 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (shake.fors_batch.recover.closure_5 N))
  := do
  let (a, a1, a2) := c
  let i ← Array.index_usize a tupled_args
  let i1 ← lift (i &&& 1#u32)
  if i1 = 0#u32
  then let a3 ← Array.index_usize a1 tupled_args
       ok (a3, c)
  else let a3 ← Array.index_usize a2 tupled_args
       ok (a3, c)

def
  shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_5 N) (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def
  shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_5 N) Std.Usize (Array Std.U8 N) := {
  call_once :=
    shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def
  shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_5
  N) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_4 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (shake.fors_batch.recover.closure_4 N))
  := do
  let (s, i, i1) := c
  let i2 ← tupled_args * i
  let i3 ← lift (UScalar.cast .Usize i1)
  let i4 ← i2 + i3
  let i5 ← i4 + 1#usize
  let a ← util.block N s i5
  ok (a, c)

def
  shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_4 N) (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def
  shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_4 N) Std.Usize (Array Std.U8 N) := {
  call_once :=
    shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def
  shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_4
  N) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_3 N)
  (tupled_args : Std.U32) :
  Result (address.Adrs × (shake.fors_batch.recover.closure_3 N))
  := do
  let a ← address.Adrs.with_word2 c 0#u32
  let a1 ← address.Adrs.with_word3 a tupled_args
  ok (a1, c)

def
  shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_3 N) (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_3 N) Std.U32 address.Adrs := {
  call_once :=
    shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_3
  N) Std.U32 address.Adrs := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
    N
  call_mut :=
    shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def
  shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_2 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (shake.fors_batch.recover.closure_2 N))
  := do
  let (s, i) := c
  let i1 ← tupled_args * i
  let a ← util.block N s i1
  ok (a, c)

def
  shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_2 N) (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def
  shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_2 N) Std.Usize (Array Std.U8 N) := {
  call_once :=
    shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def
  shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_2
  N) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_1 N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (shake.fors_batch.recover.closure_1 N))
  := do
  let (p, s) := c
  let i ← lift (UScalar.cast .U32 tupled_args)
  let i1 ← i <<< p.a
  let i2 ← Slice.index_usize s tupled_args
  let i3 ← i1 + i2
  ok (i3, c)

def
  shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure_1 N) (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnOnce
  (shake.fors_batch.recover.closure_1 N) Std.Usize Std.U32 := {
  call_once :=
    shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure_1
  N) Std.Usize Std.U32 := {
  FnOnceInst :=
    shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    N
  call_mut :=
    shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

def
  shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  {N : Std.Usize} (c : shake.fors_batch.recover.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.Usize × (shake.fors_batch.recover.closure N))
  := do
  let (i, i1) := c
  let i2 ← i1 - 1#usize
  let i3 ← lift (core.cmp.impls.OrdUsize.min tupled_args i2)
  let i4 ← i + i3
  ok (i4, c)

def
  shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
  {N : Std.Usize} (c : shake.fors_batch.recover.closure N) (i : Std.Usize) :
  Result Std.Usize
  := do
  let (i1, _) ←
    shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
  (N : Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.recover.closure
  N) Std.Usize Std.Usize := {
  call_once :=
    shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
}

@[reducible]
def shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize
  (N : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.recover.closure
  N) Std.Usize Std.Usize := {
  FnOnceInst :=
    shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
    N
  call_mut :=
    shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
}

@[rust_loop_body]
def shake.fors_batch.recover_loop0_loop0.body
  {N : Std.Usize} (sig : Slice Std.U8) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (trees : Array Std.Usize machine.width)
  (iter : core.ops.range.Range Std.U32) (indices : Array Std.U32 machine.width)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array Std.U32
    machine.width) × (Array (Array Std.U8 N) machine.width)) (Array (Array Std.U8 N)
    machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done values)
  | some j =>
    let siblings ←
      core.array.Array.map
        (shake.fors_batch.recover.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) trees (sig, stride, j)
    let left ←
      core.array.from_fn machine.width
        (shake.fors_batch.recover.closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) (indices, values, siblings)
    let right ←
      core.array.from_fn machine.width
        (shake.fors_batch.recover.closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) (indices, siblings, values)
    let indices1 ←
      core.array.Array.map
        (shake.fors_batch.recover.closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices ()
    let a ←
      core.array.Array.map
        (shake.fors_batch.recover.closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs
        N) indices1
        ({
           layer := i,
           tree := i1,
           typ := i2,
           keypair := i3,
           word2 := i4,
           word3 := i5
         }, j)
    let values1 ← shake.batch.pair seed a left right
    ok (cont (iter1, indices1, values1))

@[rust_loop]
def shake.fors_batch.recover_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sig : Slice Std.U8)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (trees : Array Std.Usize machine.width) (indices : Array Std.U32 machine.width)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, indices1, values1) =>
      shake.fors_batch.recover_loop0_loop0.body sig seed i i1 i2 i3 i4 i5
      stride trees iter1 indices1 values1)
    (iter, indices, values)

@[rust_loop_body]
def shake.fors_batch.recover_loop0_loop1.body
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result (ControlFlow ((core.slice.iter.Iter (Array Std.U8 N)) ×
    stream.State) stream.State)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done pk)
  | some value =>
    let s ← lift (Array.to_slice value)
    let pk1 ← stream.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def shake.fors_batch.recover_loop0_loop1
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => shake.fors_batch.recover_loop0_loop1.body iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def shake.fors_batch.recover_loop0.body
  {N : Std.Usize} (i : Std.Usize) (i1 : Std.U32) (i2 : Std.U32) (i3 : Std.U32)
  (i4 : Std.U32) (i5 : Std.U32) (i6 : Std.Usize) (selections : Slice Std.U32)
  (sig : Slice Std.U8) (seed : Array Std.U8 N) (i7 : Std.U32) (i8 : Std.U64)
  (i9 : Std.U32) (i10 : Std.U32) (i11 : Std.U32) (i12 : Std.U32)
  (stride : Std.Usize)
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
  | some first =>
    let i13 := Slice.len selections
    let i14 ← i13 - first
    let active ←
      lift (core.cmp.impls.OrdUsize.min i14 machine.width)
    let trees ←
      core.array.from_fn machine.width
        (shake.fors_batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize
        N) (first, active)
    let indices ←
      core.array.Array.map
        (shake.fors_batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        N) trees
        ({ n := i, h := i1, d := i2, hp := i3, a := i4, k := i5, m := i6 },
        selections)
    let leaves ←
      core.array.Array.map
        (shake.fors_batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) trees (sig, stride)
    let a ←
      core.array.Array.map
        (shake.fors_batch.recover.closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs
        N) indices
        {
          layer := i7,
          tree := i8,
          typ := i9,
          keypair := i10,
          word2 := i11,
          word3 := i12
        }
    let values ← shake.batch.short seed a leaves
    let values1 ←
      shake.fors_batch.recover_loop0_loop0 { start := 0#u32, «end» := i4 }
        sig seed i7 i8 i9 i10 i11 i12 stride trees indices values
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
        values1 { «end» := active }
    let iter2 ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    let pk1 ← shake.fors_batch.recover_loop0_loop1 iter2 pk
    ok (cont (iter1, pk1))

@[rust_loop]
def shake.fors_batch.recover_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (i : Std.Usize) (i1 : Std.U32) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (i6 : Std.Usize) (selections : Slice Std.U32)
  (sig : Slice Std.U8) (seed : Array Std.U8 N) (i7 : Std.U32) (i8 : Std.U64)
  (i9 : Std.U32) (i10 : Std.U32) (i11 : Std.U32) (i12 : Std.U32)
  (stride : Std.Usize) (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => shake.fors_batch.recover_loop0.body i i1 i2 i3 i4 i5
      i6 selections sig seed i7 i8 i9 i10 i11 i12 stride iter1 pk1)
    (iter, pk)

def shake.fors_batch.recover
  {N : Std.Usize} (p : params.Params) (selections : Slice Std.U32)
  (sig : Slice Std.U8) (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← lift (UScalar.cast .Usize p.a)
  let stride ← i + 1#usize
  let a ← address.Adrs.with_type addr address.FORS_ROOTS
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let pk ← stream.start seed a1
  let i1 := Slice.len selections
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := i1 } machine.width
  let pk1 ←
    shake.fors_batch.recover_loop0 iter p.n p.h p.d p.hp p.a p.k p.m selections
      sig seed addr.layer addr.tree addr.typ addr.keypair addr.word2
      addr.word3 stride pk
  stream.digest N pk1
end
end slhdsa.ShakeBatch
