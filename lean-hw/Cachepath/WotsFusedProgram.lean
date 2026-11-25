import Cachepath.WotsRows
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open ShakeBatch
set_option linter.concreteInstances false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
noncomputable section
variable [machine : Machine]

@[reducible]
def generate.closure.closure (N : Std.Usize) :=
  address.Adrs × Std.U32

@[reducible]
def generate.closure (N : Std.Usize) :=
  Array Std.U32 machine.width × address.Adrs

def
  generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize}
  (c : generate.closure.closure N)
  (tupled_args : Std.U32) :
  Result (address.Adrs ×
    (generate.closure.closure N))
  := do
  let (a, i) := c
  let a1 ← address.Adrs.with_type a i
  let a2 ← address.Adrs.with_keypair a1 tupled_args
  ok (a2, c)

def
  generate.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize}
  (c : generate.closure.closure N) (i : Std.U32)
  :
  Result address.Adrs
  := do
  let (a, _) ←
    generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def
  generate.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (generate.closure.closure N) Std.U32
  address.Adrs := {
  call_once :=
    generate.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def
  generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnMut
  (generate.closure.closure N) Std.U32
  address.Adrs := {
  FnOnceInst :=
    generate.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
    N
  call_mut :=
    generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def
  generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call
  {N : Std.Usize} (c : generate.closure N)
  (tupled_args : Std.U32) :
  Result (Array address.Adrs machine.width)
  := do
  let (a, a1) := c
  core.array.Array.map
    (generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs
    N) a (a1, tupled_args)

@[rust_loop_body]
def generate_loop0_loop0.body
  (i : Std.Usize) (offset : Std.Usize) (id : Std.U64)
  (iter : core.ops.range.Range Std.U32)
  (input : Array (Array Std.U64 machine.width) 25#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Array Std.U64
    machine.width) 25#usize) × (Array (Array Std.U64 machine.width) 25#usize)) ((Array
    (Array Std.U64 machine.width) 25#usize) × (Array (Array Std.U64 machine.width)
    25#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done (input, state))
  | some step =>
    let i1 ← core.num.U32.swap_bytes step
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let i3 ← i2 <<< 32#i32
    let i4 ← lift (id ||| i3)
    let i5 ← offset - 1#usize
    let a := Array.repeat machine.width i4
    let input1 ← Array.update input i5 a
    let i6 ← offset + i
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
        input1 { start := offset, «end» := i6 }
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U64 machine.width)))
        state { «end» := i }
    let s2 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy machine.width
        core.marker.CopyU64) s s1
    let input2 := index_mut_back s2
    let input3 ← machine.permute input2
    ok (cont (iter1, input2, input3))

@[rust_loop]
def generate_loop0_loop0
  (i : Std.Usize) (iter : core.ops.range.Range Std.U32) (offset : Std.Usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) (id : Std.U64)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result ((Array (Array Std.U64 machine.width) 25#usize) × (Array (Array Std.U64
    machine.width) 25#usize))
  := do
  loop
    (fun (iter1, input1, state1) =>
      generate_loop0_loop0.body i offset id iter1
      input1 state1)
    (iter, input, state)

@[rust_loop_body]
def generate_loop0_loop1_loop0.body
  (pos : Std.Usize) (word : Array Std.U64 machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some lane =>
    let i ← Array.index_usize word lane
    let a ← Array.index_usize pk pos
    let i1 ← Array.index_usize a lane
    let i2 ← lift (i1 ^^^ i)
    let (a1, index_mut_back) ← Array.index_mut_usize pk pos
    let a2 ← Array.update a1 lane i2
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def generate_loop0_loop1_loop0
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 machine.width) 25#usize) (pos : Std.Usize)
  (word : Array Std.U64 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, pk1) =>
      generate_loop0_loop1_loop0.body pos word
      iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def generate_loop0_loop1.body
  (iter : core.slice.iter.Iter (Array Std.U64 machine.width))
  (pk : Array (Array Std.U64 machine.width) 25#usize) (pos : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.Iter (Array Std.U64 machine.width)) × (Array
    (Array Std.U64 machine.width) 25#usize) × Std.Usize) ((Array (Array Std.U64
    machine.width) 25#usize) × Std.Usize))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (pk, pos))
  | some word =>
    let pk1 ←
      generate_loop0_loop1_loop0
        { start := 0#usize, «end» := machine.width } pk pos word
    let pos1 ← pos + 1#usize
    if pos1 = 17#usize
    then
      let pk2 ← machine.permute pk1
      ok (cont (iter1, pk2, 0#usize))
    else ok (cont (iter1, pk1, pos1))

@[rust_loop]
def generate_loop0_loop1
  (iter : core.slice.iter.Iter (Array Std.U64 machine.width))
  (pk : Array (Array Std.U64 machine.width) 25#usize) (pos : Std.Usize) :
  Result ((Array (Array Std.U64 machine.width) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1) =>
      generate_loop0_loop1.body iter1 pk1 pos1)
    (iter, pk, pos)

@[rust_loop_body]
def generate_loop0.body
  (i : Std.Usize) (offset : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 machine.width) 25#usize) (pos : Std.Usize)
  (prf : Array (Array Std.U64 machine.width) 25#usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize) × Std.Usize × (Array (Array Std.U64 machine.width)
    25#usize) × (Array (Array Std.U64 machine.width) 25#usize)) ((Array (Array
    Std.U64 machine.width) 25#usize) × Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (pk, pos))
  | some chain =>
    let i1 ← lift (UScalar.cast .U32 chain)
    let i2 ← core.num.U32.swap_bytes i1
    let id ← lift (core.convert.num.FromU64U32.from i2)
    let i3 ← offset - 1#usize
    let a := Array.repeat machine.width id
    let prf1 ← Array.update prf i3 a
    let prf2 ← machine.permute prf1
    let i4 ← params.W - 1#u32
    let (input1, state) ←
      generate_loop0_loop0 i
        { start := 0#u32, «end» := i4 } offset input id prf2
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U64 machine.width)))
        state { «end» := i }
    let iter2 ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    let (pk1, pos1) ←
      generate_loop0_loop1 iter2 pk pos
    ok (cont (iter1, pk1, pos1, prf1, input1))

@[rust_loop]
def generate_loop0
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (pk : Array (Array Std.U64 machine.width) 25#usize) (pos : Std.Usize)
  (prf : Array (Array Std.U64 machine.width) 25#usize)
  (input : Array (Array Std.U64 machine.width) 25#usize) :
  Result ((Array (Array Std.U64 machine.width) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1, prf1, input1) =>
      generate_loop0.body i offset iter1 pk1 pos1
      prf1 input1)
    (iter, pk, pos, prf, input)

@[rust_loop_body]
def generate_loop1.body
  (pos : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some lane =>
    let a ← Array.index_usize pk pos
    let i ← Array.index_usize a lane
    let i1 ← lift (i ^^^ 31#u64)
    let (a1, index_mut_back) ← Array.index_mut_usize pk pos
    let a2 ← Array.update a1 lane i1
    let i2 ← 1#u64 <<< 63#i32
    let pk1 := index_mut_back a2
    let a3 ← Array.index_usize pk1 16#usize
    let i3 ← Array.index_usize a3 lane
    let i4 ← lift (i3 ^^^ i2)
    let (a4, index_mut_back1) ← Array.index_mut_usize pk1 16#usize
    let a5 ← Array.update a4 lane i4
    let a6 := index_mut_back1 a5
    ok (cont (iter1, a6))

@[rust_loop]
def generate_loop1
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 machine.width) 25#usize) (pos : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => generate_loop1.body pos
      iter1 pk1)
    (iter, pk)

def generate
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (keys : Array Std.U32 machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let i ← N / 8#usize
  let offset ← i + 4#usize
  let a ←
    generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N)
      (keys, addr) address.WOTS_PK
  let i1 ← N + 32#usize
  let pk ← ShakeBatch.shake.batch.header seed a i1
  let a1 := Array.repeat machine.width 0#u64
  let pk1 ← Array.update pk offset a1
  let a2 := Array.repeat machine.width 0#u64
  let a3 ← Array.update pk1 16#usize a2
  let a4 ←
    generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N)
      (keys, addr) address.WOTS_PRF
  let i2 ← 2#usize * N
  let i3 ← i2 + 32#usize
  let prf ← ShakeBatch.shake.batch.header seed a4 i3
  let a5 := Array.repeat machine.width sk
  let prf1 ← ShakeBatch.shake.batch.put prf offset a5
  let a6 ←
    generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N)
      (keys, addr) address.WOTS_HASH
  let i4 ← i2 + 32#usize
  let input ← ShakeBatch.shake.batch.header seed a6 i4
  let i5 ← i2 + params.LEN2
  let (pk2, pos) ←
    generate_loop0 i
      { start := 0#usize, «end» := i5 } offset a3 offset prf1 input
  let pk3 ←
    generate_loop1
      { start := 0#usize, «end» := machine.width } pk2 pos
  let pk4 ← machine.permute pk3
  ShakeBatch.shake.batch.read N pk4

@[instance_reducible] def leaves : Leaves machine where
  gen := generate

end
end slhdsa.cache.builder.nativeShake.Vector.Fused
