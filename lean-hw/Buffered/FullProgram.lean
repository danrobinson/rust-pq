import Fused.Forest
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Buffered.Full
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance : Machine := Fused.machine kernel

@[reducible]
def leaves.closure_2 (N : Std.Usize) := Std.U32


@[reducible]
def leaves.closure_1 (N : Std.Usize) := Std.U32


@[reducible]
def leaves.closure (N : Std.Usize) := Std.U32


def
  leaves.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : leaves.closure_2 N)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × (leaves.closure_2 N))
  := do
  let i ← ShakeBatch.core.num.U32.swap_bytes address.WOTS_HASH
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← lift (UScalar.cast .U32 tupled_args)
  let i3 ← c + i2
  let i4 ← ShakeBatch.core.num.U32.swap_bytes i3
  let i5 ← lift (core.convert.num.FromU64U32.from i4)
  let i6 ← i5 <<< 32#i32
  let i7 ← lift (i1 ||| i6)
  ok (i7, c)


def
  leaves.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : leaves.closure_2 N)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    leaves.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1


@[reducible]
def
  leaves.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnOnce
  (leaves.closure_2 N) Std.Usize Std.U64 := {
  call_once :=
    leaves.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}


@[reducible]
def
  leaves.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnMut
  (leaves.closure_2 N) Std.Usize Std.U64 := {
  FnOnceInst :=
    leaves.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
    N
  call_mut :=
    leaves.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}


def
  leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : leaves.closure_1 N)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × (leaves.closure_1 N))
  := do
  let i ← ShakeBatch.core.num.U32.swap_bytes address.WOTS_PRF
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← lift (UScalar.cast .U32 tupled_args)
  let i3 ← c + i2
  let i4 ← ShakeBatch.core.num.U32.swap_bytes i3
  let i5 ← lift (core.convert.num.FromU64U32.from i4)
  let i6 ← i5 <<< 32#i32
  let i7 ← lift (i1 ||| i6)
  ok (i7, c)


def
  leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : leaves.closure_1 N)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1


@[reducible]
def
  leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnOnce
  (leaves.closure_1 N) Std.Usize Std.U64 := {
  call_once :=
    leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}


@[reducible]
def
  leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnMut
  (leaves.closure_1 N) Std.Usize Std.U64 := {
  FnOnceInst :=
    leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
    N
  call_mut :=
    leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}


def
  leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : leaves.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × (leaves.closure N))
  := do
  let i ← ShakeBatch.core.num.U32.swap_bytes address.WOTS_PK
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← lift (UScalar.cast .U32 tupled_args)
  let i3 ← c + i2
  let i4 ← ShakeBatch.core.num.U32.swap_bytes i3
  let i5 ← lift (core.convert.num.FromU64U32.from i4)
  let i6 ← i5 <<< 32#i32
  let i7 ← lift (i1 ||| i6)
  ok (i7, c)


def
  leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : leaves.closure N) (i : Std.Usize)
  :
  Result Std.U64
  := do
  let (i1, _) ←
    leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1


@[reducible]
def
  leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnOnce
  (leaves.closure N) Std.Usize Std.U64 := {
  call_once :=
    leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}


@[reducible]
def
  leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnMut
  (leaves.closure N) Std.Usize Std.U64 := {
  FnOnceInst :=
    leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
    N
  call_mut :=
    leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}


@[rust_loop_body]
def leaves_loop0.body
  (sw : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some j =>
    let i ← Array.index_usize sw j
    let a := Array.repeat 8#usize i
    let a1 ← Array.update pk j a
    ok (cont (iter1, a1))


@[rust_loop]
def leaves_loop0
  (iter : core.ops.range.Range Std.Usize) (sw : Array Std.U64 4#usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => leaves_loop0.body sw iter1 pk1)
    (iter, pk)


@[rust_loop_body]
def leaves_loop1_loop0.body
  (N : Std.Usize) (sw : Array Std.U64 4#usize) (w0 : Std.U64) (w1 : Std.U64)
  (w2_hash : Array Std.U64 8#usize) (id : Std.U64)
  (iter : core.ops.range.Range Std.U32)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Array Std.U64
    8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done state)
  | some step =>
    let i ← ShakeBatch.core.num.U32.swap_bytes step
    let i1 ← lift (core.convert.num.FromU64U32.from i)
    let i2 ← i1 <<< 32#i32
    let i3 ← lift (id ||| i2)
    let w3 := Array.repeat 8#usize i3
    let state1 ← NativeShakeWots.refill_short_inplace N state sw w0 w1 w2_hash w3
    let state2 ← kernel.permute state1
    ok (cont (iter1, state2))


@[rust_loop]
def leaves_loop1_loop0
  (N : Std.Usize) (iter : core.ops.range.Range Std.U32)
  (sw : Array Std.U64 4#usize) (w0 : Std.U64) (w1 : Std.U64)
  (w2_hash : Array Std.U64 8#usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) (id : Std.U64) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, state1) => leaves_loop1_loop0.body N sw
      w0 w1 w2_hash id iter1 state1)
    (iter, state)


@[rust_loop_body]
def leaves_loop1_loop1_loop0.body
  (pos : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize)
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some lane =>
    let a ← Array.index_usize state j
    let i ← Array.index_usize a lane
    let a1 ← Array.index_usize pk pos
    let i1 ← Array.index_usize a1 lane
    let i2 ← lift (i1 ^^^ i)
    let (a2, index_mut_back) ← Array.index_mut_usize pk pos
    let a3 ← Array.update a2 lane i2
    let a4 := index_mut_back a3
    ok (cont (iter1, a4))


@[rust_loop]
def leaves_loop1_loop1_loop0
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) (j : Std.Usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => leaves_loop1_loop1_loop0.body
      pos state j iter1 pk1)
    (iter, pk)


@[rust_loop_body]
def leaves_loop1_loop1.body
  (state : Array (Array Std.U64 8#usize) 25#usize)
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize) × Std.Usize) ((Array (Array Std.U64 8#usize)
    25#usize) × Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (pk, pos))
  | some j =>
    let i ← (ok 8#usize : Result Usize)
    let pk1 ←
      leaves_loop1_loop1_loop0
        { start := 0#usize, «end» := i } pk pos state j
    let pos1 ← pos + 1#usize
    if pos1 = 17#usize
    then
      let pk2 ← kernel.permute pk1
      ok (cont (iter1, pk2, 0#usize))
    else ok (cont (iter1, pk1, pos1))


@[rust_loop]
def leaves_loop1_loop1
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1) => leaves_loop1_loop1.body
      state iter1 pk1 pos1)
    (iter, pk, pos)


@[rust_loop_body]
def leaves_loop1.body
  (N : Std.Usize) (n : Std.Usize) (sw : Array Std.U64 4#usize)
  (skw : Array Std.U64 4#usize) (w0 : Std.U64) (w1 : Std.U64)
  (w2_prf : Array Std.U64 8#usize) (w2_hash : Array Std.U64 8#usize)
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize) × Std.Usize × (Array (Array Std.U64 8#usize)
    25#usize)) ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (pk, pos))
  | some chain =>
    let i ← lift (UScalar.cast .U32 chain)
    let i1 ← ShakeBatch.core.num.U32.swap_bytes i
    let id ← lift (core.convert.num.FromU64U32.from i1)
    let w3_id := Array.repeat 8#usize id
    let state1 ← NativeShakeWots.fill_prf N state sw skw w0 w1 w2_prf w3_id
    let state2 ← kernel.permute state1
    let i2 ← params.W - 1#u32
    let state3 ←
      leaves_loop1_loop0 N
        { start := 0#u32, «end» := i2 } sw w0 w1 w2_hash state2 id
    let (pk1, pos1) ←
      leaves_loop1_loop1
        { start := 0#usize, «end» := n } pk pos state3
    ok (cont (iter1, pk1, pos1, state3))


@[rust_loop]
def leaves_loop1
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize) (n : Std.Usize)
  (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize) (w0 : Std.U64)
  (w1 : Std.U64) (w2_prf : Array Std.U64 8#usize)
  (w2_hash : Array Std.U64 8#usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1, state1) => leaves_loop1.body
      N n sw skw w0 w1 w2_prf w2_hash iter1 pk1 pos1 state1)
    (iter, pk, pos, state)


@[rust_loop_body]
def leaves_loop2.body
  (pos : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
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
def leaves_loop2
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => leaves_loop2.body pos iter1
      pk1)
    (iter, pk)


def leaves
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (first_key : Std.U32) (addr : address.Adrs) :
  Result (Array (Array Std.U8 N) 8#usize)
  := do
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let sw ← NativeVerify.seed_words seed
  let skw ← NativeVerify.seed_words sk
  let base ← NativeVerify.adrs_words addr
  let w0 ← Array.index_usize base 0#usize
  let w1 ← Array.index_usize base 1#usize
  let w2_pk ←
    core.array.from_fn 8#usize
      (leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      N) first_key
  let w2_prf ←
    core.array.from_fn 8#usize
      (leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      N) first_key
  let w2_hash ←
    core.array.from_fn 8#usize
      (leaves.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      N) first_key
  let a := Array.repeat 8#usize 0#u64
  let pk := Array.repeat 25#usize a
  let pk1 ←
    leaves_loop0 { start := 0#usize, «end» := n } sw
      pk
  let a1 := Array.repeat 8#usize w0
  let pk2 ← Array.update pk1 n a1
  let i ← n + 1#usize
  let a2 := Array.repeat 8#usize w1
  let pk3 ← Array.update pk2 i a2
  let i1 ← n + 2#usize
  let a3 ← Array.update pk3 i1 w2_pk
  let a4 := Array.repeat 8#usize 0#u64
  let state := Array.repeat 25#usize a4
  let i2 ← 2#usize * N
  let i3 ← i2 + params.LEN2
  let (pk4, pos) ←
    leaves_loop1 N { start := 0#usize, «end» := i3 } n
      sw skw w0 w1 w2_prf w2_hash a3 offset state
  let i4 ← (ok 8#usize : Result Usize)
  let pk5 ←
    leaves_loop2 { start := 0#usize, «end» := i4 } pk4
      pos
  let pk6 ← kernel.permute pk5
  NativeVerify.ActiveHash.read_active N pk6 i4

end slhdsa.Buffered.Full
