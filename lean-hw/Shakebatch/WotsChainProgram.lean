import Shakebatch.Program
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine]

/-- The Rust standard library's 32-bit byte swap. -/
def core.num.U32.swap_bytes (x : U32) : Result U32 :=
  ok ⟨x.bv.extractLsb' 0 8 ++ x.bv.extractLsb' 8 8 ++ x.bv.extractLsb' 16 8 ++ x.bv.extractLsb' 24 8⟩

def shake.batch.secrets.closure (N : Std.Usize) :=
  address.Adrs × Array Std.Usize machine.width

def shake.batch.chains.closure (N : Std.Usize) :=
  address.Adrs × Array Std.Usize machine.width

def
  shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
  {N : Std.Usize} (c : shake.batch.secrets.closure N) (tupled_args : Std.Usize)
  :
  Result (address.Adrs × (shake.batch.secrets.closure N))
  := do
  let (a, a1) := c
  let i ← Array.index_usize a1 tupled_args
  let i1 ← lift (UScalar.cast .U32 i)
  let a2 ← address.Adrs.with_word2 a i1
  ok (a2, c)

def
  shake.batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
  {N : Std.Usize} (c : shake.batch.secrets.closure N) (i : Std.Usize) :
  Result address.Adrs
  := do
  let (a, _) ←
    shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
      c i
  ok a

@[reducible]
def shake.batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.secrets.closure N)
  Std.Usize address.Adrs := {
  call_once :=
    shake.batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
}

@[reducible]
def shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.secrets.closure N)
  Std.Usize address.Adrs := {
  FnOnceInst :=
    shake.batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs N
  call_mut :=
    shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
}

def shake.batch.secrets
  {N : Std.Usize} (seed : Array Std.U8 N) (sk : Array Std.U8 N)
  (addr : address.Adrs) (ids : Array Std.Usize machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let a ← address.Adrs.with_type addr address.WOTS_PRF
  let prf ← address.Adrs.with_keypair a addr.keypair
  let addresses ←
    core.array.from_fn machine.width
      (shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N)
      (prf, ids)
  let a1 := Array.repeat machine.width sk
  shake.batch.short seed addresses a1

def
  shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
  {N : Std.Usize} (c : shake.batch.chains.closure N) (tupled_args : Std.Usize)
  :
  Result (address.Adrs × (shake.batch.chains.closure N))
  := do
  let (a, a1) := c
  let i ← Array.index_usize a1 tupled_args
  let i1 ← lift (UScalar.cast .U32 i)
  let a2 ← address.Adrs.with_word2 a i1
  let a3 ← address.Adrs.with_word3 a2 0#u32
  ok (a3, c)

def
  shake.batch.chains.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
  {N : Std.Usize} (c : shake.batch.chains.closure N) (i : Std.Usize) :
  Result address.Adrs
  := do
  let (a, _) ←
    shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
      c i
  ok a

@[reducible]
def shake.batch.chains.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs (N :
  Std.Usize) : core.ops.function.FnOnce (shake.batch.chains.closure N)
  Std.Usize address.Adrs := {
  call_once :=
    shake.batch.chains.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
}

@[reducible]
def shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs (N :
  Std.Usize) : core.ops.function.FnMut (shake.batch.chains.closure N) Std.Usize
  address.Adrs := {
  FnOnceInst :=
    shake.batch.chains.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs N
  call_mut :=
    shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
}

@[rust_loop_body]
def shake.batch.chains_loop0_loop0.body
  (index : Array Std.U32 machine.width) (offset : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (output : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done output)
  | some lane =>
    let i ← Array.index_usize index lane
    let i1 ← core.num.U32.swap_bytes i
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let i3 ← i2 <<< 32#i32
    let i4 ← offset - 1#usize
    let a ← Array.index_usize output i4
    let i5 ← Array.index_usize a lane
    let i6 ← lift (i5 ||| i3)
    let (a1, index_mut_back) ← Array.index_mut_usize output i4
    let a2 ← Array.update a1 lane i6
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def shake.batch.chains_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (index : Array Std.U32 machine.width)
  (offset : Std.Usize) (output : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, output1) => shake.batch.chains_loop0_loop0.body index offset
      iter1 output1)
    (iter, output)

@[rust_loop_body]
def shake.batch.chains_loop0_loop1_loop0.body
  (offset : Std.Usize) (output : Array (Array Std.U64 machine.width) 25#usize)
  (lane : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done input)
  | some j =>
    let a ← Array.index_usize output j
    let i ← Array.index_usize a lane
    let i1 ← offset + j
    let (a1, index_mut_back) ← Array.index_mut_usize input i1
    let a2 ← Array.update a1 lane i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def shake.batch.chains_loop0_loop1_loop0
  (iter : core.ops.range.Range Std.Usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (output : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, input1) => shake.batch.chains_loop0_loop1_loop0.body offset
      output lane iter1 input1)
    (iter, input)

@[rust_loop_body]
def shake.batch.chains_loop0_loop1.body
  (i : Std.Usize) («end» : Array Std.U32 machine.width) (offset : Std.Usize)
  (output : Array (Array Std.U64 machine.width) 25#usize)
  (iter : core.ops.range.Range Std.Usize) (index : Array Std.U32 machine.width)
  (input : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    machine.width) × (Array (Array Std.U64 machine.width) 25#usize)) ((Array Std.U32
    machine.width) × (Array (Array Std.U64 machine.width) 25#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (index, input))
  | some lane =>
    let i1 ← Array.index_usize index lane
    let i2 ← Array.index_usize «end» lane
    if i1 < i2
    then
      let input1 ←
        shake.batch.chains_loop0_loop1_loop0 { start := 0#usize, «end» := i }
          input offset output lane
      let i3 ← Array.index_usize index lane
      let i4 ← i3 + 1#u32
      let a ← Array.update index lane i4
      ok (cont (iter1, a, input1))
    else ok (cont (iter1, index, input))

@[rust_loop]
def shake.batch.chains_loop0_loop1
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (index : Array Std.U32 machine.width) («end» : Array Std.U32 machine.width)
  (input : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (output : Array (Array Std.U64 machine.width) 25#usize) :
  Result ((Array Std.U32 machine.width) × (Array (Array Std.U64 machine.width) 25#usize))
  := do
  loop
    (fun (iter1, index1, input1) => shake.batch.chains_loop0_loop1.body i
      «end» offset output iter1 index1 input1)
    (iter, index, input)

@[rust_loop_body]
def shake.batch.chains_loop0.body
  (i : Std.Usize) («end» : Array Std.U32 machine.width) (offset : Std.Usize)
  (index : Array Std.U32 machine.width)
  (input : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((Array Std.U32 machine.width) × (Array (Array Std.U64
    machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let b ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU32 index «end»
  if b
  then
    let output ←
      shake.batch.chains_loop0_loop0
        { start := 0#usize, «end» := machine.width } index offset
        input
    let output1 ← machine.permute output
    let (index1, input1) ←
      shake.batch.chains_loop0_loop1 i
        { start := 0#usize, «end» := machine.width } index «end»
        input offset output1
    ok (cont (index1, input1))
  else ok (done input)

@[rust_loop]
def shake.batch.chains_loop0
  (i : Std.Usize) (index : Array Std.U32 machine.width)
  («end» : Array Std.U32 machine.width)
  (input : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (index1, input1) => shake.batch.chains_loop0.body i «end» offset
      index1 input1)
    (index, input)

@[rust_loop_body]
def shake.batch.chains_loop1_loop0.body
  {N : Std.Usize} (input : Array (Array Std.U64 machine.width) 25#usize)
  (offset : Std.Usize) (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (result : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done result)
  | some lane =>
    let (a, index_mut_back) ← Array.index_mut_usize result lane
    let i ← 8#usize * j
    let i1 ← i + 8#usize
    let (s, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
        { start := i, «end» := i1 }
    let i2 ← offset + j
    let a1 ← Array.index_usize input i2
    let i3 ← Array.index_usize a1 lane
    let a2 ← lift (core.num.U64.to_le_bytes i3)
    let s1 ← lift (Array.to_slice a2)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let a3 := index_mut_back1 s2
    let a4 := index_mut_back a3
    ok (cont (iter1, a4))

@[rust_loop]
def shake.batch.chains_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (result : Array (Array Std.U8 N) machine.width) (j : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, result1) => shake.batch.chains_loop1_loop0.body input offset j
      iter1 result1)
    (iter, result)

@[rust_loop_body]
def shake.batch.chains_loop1.body
  {N : Std.Usize} (input : Array (Array Std.U64 machine.width) 25#usize)
  (offset : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (result : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done result)
  | some j =>
    let result1 ←
      shake.batch.chains_loop1_loop0
        { start := 0#usize, «end» := machine.width } input offset
        result j
    ok (cont (iter1, result1))

@[rust_loop]
def shake.batch.chains_loop1
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (result : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, result1) => shake.batch.chains_loop1.body input offset iter1
      result1)
    (iter, result)

def shake.batch.chains
  {N : Std.Usize} (seed : Array Std.U8 N) (addr : address.Adrs)
  (ids : Array Std.Usize machine.width) (values : Array (Array Std.U8 N) machine.width)
  (index : Array Std.U32 machine.width) («end» : Array Std.U32 machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let addresses ←
    core.array.from_fn machine.width
      (shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N)
      (addr, ids)
  let i ← 2#usize * N
  let i1 ← i + 32#usize
  let input ← shake.batch.header seed addresses i1
  let i2 ← N / 8#usize
  let offset ← i2 + 4#usize
  let input1 ← shake.batch.put input offset values
  let input2 ← shake.batch.chains_loop0 i2 index «end» input1 offset
  let a := Array.repeat N 0#u8
  let result := Array.repeat machine.width a
  shake.batch.chains_loop1 { start := 0#usize, «end» := i2 } input2 offset
    result
end
end slhdsa.ShakeBatch
