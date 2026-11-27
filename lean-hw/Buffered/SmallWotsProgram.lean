import Fused.Forest
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance smallLeafMachine : Machine := Fused.machine kernel

@[reducible]
def leaves.closure_1 (N : Std.Usize) (K : Std.Usize) :=
  Array (Array Std.U64 8#usize) 25#usize


@[reducible]
def leaves.closure (N : Std.Usize) (K : Std.Usize) :=
  Std.U64


def
  leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} {K : Std.Usize}
  (c : leaves.closure_1 N K) (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (leaves.closure_1 N K))
  := do
  let a ← NativeVerify.Wots.extract_lane N c 0#usize tupled_args
  ok (a, c)


def
  leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} {K : Std.Usize}
  (c : leaves.closure_1 N K) (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a


@[reducible]
def
  leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) (K : Std.Usize) : core.ops.function.FnOnce
  (leaves.closure_1 N K) Std.Usize (Array Std.U8 N) := {
  call_once :=
    leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}


@[reducible]
def
  leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) (K : Std.Usize) : core.ops.function.FnMut
  (leaves.closure_1 N K) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    leaves.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N K
  call_mut :=
    leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}


def
  leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
  {N : Std.Usize} {K : Std.Usize}
  (c : leaves.closure N K) (tupled_args : Std.U64) :
  Result (Std.U64 × (leaves.closure N K))
  := do
  let i ← lift (tupled_args ||| c)
  ok (i, c)


def
  leaves.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once
  {N : Std.Usize} {K : Std.Usize}
  (c : leaves.closure N K) (i : Std.U64) :
  Result Std.U64
  := do
  let (i1, _) ←
    leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
      c i
  ok i1


@[reducible]
def
  leaves.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64
  (N : Std.Usize) (K : Std.Usize) : core.ops.function.FnOnce
  (leaves.closure N K) Std.U64 Std.U64 := {
  call_once :=
    leaves.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once
}


@[reducible]
def leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64
  (N : Std.Usize) (K : Std.Usize) : core.ops.function.FnMut
  (leaves.closure N K) Std.U64 Std.U64 := {
  FnOnceInst :=
    leaves.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64
    N K
  call_mut :=
    leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
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
def leaves_loop1.body
  (first_key : Std.U32) (n : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some k =>
    let i ← ShakeBatch.core.num.U32.swap_bytes address.WOTS_PK
    let i1 ← lift (core.convert.num.FromU64U32.from i)
    let i2 ← lift (UScalar.cast .U32 k)
    let i3 ← first_key + i2
    let i4 ← ShakeBatch.core.num.U32.swap_bytes i3
    let i5 ← lift (core.convert.num.FromU64U32.from i4)
    let i6 ← i5 <<< 32#i32
    let i7 ← n + 2#usize
    let (a, index_mut_back) ← Array.index_mut_usize pk i7
    let i8 ← lift (i1 ||| i6)
    let a1 ← Array.update a k i8
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))


@[rust_loop]
def leaves_loop1
  (iter : core.ops.range.Range Std.Usize) (first_key : Std.U32) (n : Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => leaves_loop1.body first_key n
      iter1 pk1)
    (iter, pk)


@[rust_loop_body]
def leaves_loop2_loop0.body
  (K : Std.Usize) (first_key : Std.U32) (idx : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (w2_prf : Array Std.U64 8#usize)
  (w2_hash : Array Std.U64 8#usize) (w3_id : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    8#usize) × (Array Std.U64 8#usize) × (Array Std.U64 8#usize)) ((Array
    Std.U64 8#usize) × (Array Std.U64 8#usize) × (Array Std.U64 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (w2_prf, w2_hash, w3_id))
  | some lane =>
    let flat ← idx + lane
    let chain ← flat / K
    let k ← flat % K
    let i ← lift (UScalar.cast .U32 k)
    let i1 ← first_key + i
    let kp ← ShakeBatch.core.num.U32.swap_bytes i1
    let i2 ← ShakeBatch.core.num.U32.swap_bytes address.WOTS_PRF
    let i3 ← lift (core.convert.num.FromU64U32.from i2)
    let i4 ← lift (core.convert.num.FromU64U32.from kp)
    let i5 ← i4 <<< 32#i32
    let i6 ← lift (i3 ||| i5)
    let a ← Array.update w2_prf lane i6
    let i7 ← ShakeBatch.core.num.U32.swap_bytes address.WOTS_HASH
    let i8 ← lift (core.convert.num.FromU64U32.from i7)
    let i9 ← lift (core.convert.num.FromU64U32.from kp)
    let i10 ← i9 <<< 32#i32
    let i11 ← lift (i8 ||| i10)
    let a1 ← Array.update w2_hash lane i11
    let i12 ← lift (UScalar.cast .U32 chain)
    let i13 ← ShakeBatch.core.num.U32.swap_bytes i12
    let i14 ← lift (core.convert.num.FromU64U32.from i13)
    let a2 ← Array.update w3_id lane i14
    ok (cont (iter1, a, a1, a2))


@[rust_loop]
def leaves_loop2_loop0
  (K : Std.Usize) (iter : core.ops.range.Range Std.Usize) (first_key : Std.U32)
  (idx : Std.Usize) (w2_prf : Array Std.U64 8#usize)
  (w2_hash : Array Std.U64 8#usize) (w3_id : Array Std.U64 8#usize) :
  Result ((Array Std.U64 8#usize) × (Array Std.U64 8#usize) × (Array Std.U64
    8#usize))
  := do
  loop
    (fun (iter1, w2_prf1, w2_hash1, w3_id1) =>
      leaves_loop2_loop0.body K first_key idx iter1
      w2_prf1 w2_hash1 w3_id1)
    (iter, w2_prf, w2_hash, w3_id)


@[rust_loop_body]
def leaves_loop2_loop1.body
  (N : Std.Usize) (K : Std.Usize) (sw : Array Std.U64 4#usize) (w0 : Std.U64)
  (w1 : Std.U64) (active : Std.Usize) (w2_hash : Array Std.U64 8#usize)
  (w3_id : Array Std.U64 8#usize) (iter : core.ops.range.Range Std.U32)
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
    let step_hi ← i1 <<< 32#i32
    let w3 ←
      core.array.Array.map
        (leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64
        N K) w3_id step_hi
    let state1 ← NativeShakeWots.refill_short_inplace N state sw w0 w1 w2_hash w3
    let state2 ← kernel.active state1 active
    ok (cont (iter1, state2))


@[rust_loop]
def leaves_loop2_loop1
  (N : Std.Usize) (K : Std.Usize) (iter : core.ops.range.Range Std.U32)
  (sw : Array Std.U64 4#usize) (w0 : Std.U64) (w1 : Std.U64)
  (state : Array (Array Std.U64 8#usize) 25#usize) (active : Std.Usize)
  (w2_hash : Array Std.U64 8#usize) (w3_id : Array Std.U64 8#usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, state1) => leaves_loop2_loop1.body N K
      sw w0 w1 active w2_hash w3_id iter1 state1)
    (iter, state)


@[rust_loop_body]
def leaves_loop2_loop2_loop0_loop0.body
  (pos : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize)
  (group : Std.Usize) (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some k =>
    massert (j < 25#usize)
    let i ← group + k
    let a ← Array.index_usize state j
    let i1 ← Array.index_usize a i
    let a1 ← Array.index_usize pk pos
    let i2 ← Array.index_usize a1 k
    let i3 ← lift (i2 ^^^ i1)
    let (a2, index_mut_back) ← Array.index_mut_usize pk pos
    let a3 ← Array.update a2 k i3
    let a4 := index_mut_back a3
    ok (cont (iter1, a4))


@[rust_loop]
def leaves_loop2_loop2_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) (group : Std.Usize)
  (j : Std.Usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) =>
      leaves_loop2_loop2_loop0_loop0.body pos state
      group j iter1 pk1)
    (iter, pk)


@[rust_loop_body]
def leaves_loop2_loop2_loop0.body
  (K : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize)
  (group : Std.Usize) (iter : core.ops.range.Range Std.Usize)
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
    let pk1 ←
      leaves_loop2_loop2_loop0_loop0
        { start := 0#usize, «end» := K } pk pos state group j
    let pos1 ← pos + 1#usize
    if pos1 = 17#usize
    then
      let pk2 ← kernel.active pk1 K
      ok (cont (iter1, pk2, 0#usize))
    else ok (cont (iter1, pk1, pos1))


@[rust_loop]
def leaves_loop2_loop2_loop0
  (K : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) (group : Std.Usize) :
  Result ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1) =>
      leaves_loop2_loop2_loop0.body K state group iter1
      pk1 pos1)
    (iter, pk, pos)


@[rust_loop_body]
def leaves_loop2_loop2.body
  (K : Std.Usize) (n : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
    ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (pk, pos))
  | some group =>
    let (pk1, pos1) ←
      leaves_loop2_loop2_loop0 K
        { start := 0#usize, «end» := n } pk pos state group
    ok (cont (iter1, pk1, pos1))


@[rust_loop]
def leaves_loop2_loop2
  (K : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (n : Std.Usize) (pk : Array (Array Std.U64 8#usize) 25#usize)
  (pos : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1) => leaves_loop2_loop2.body K
      n state iter1 pk1 pos1)
    (iter, pk, pos)


@[rust_loop_body]
def leaves_loop2.body
  (N : Std.Usize) (K : Std.Usize) (first_key : Std.U32) (total : Std.Usize)
  (n : Std.Usize) (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (w0 : Std.U64) (w1 : Std.U64) (pk : Array (Array Std.U64 8#usize) 25#usize)
  (pos : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize)
  (idx : Std.Usize) :
  Result (ControlFlow ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize ×
    (Array (Array Std.U64 8#usize) 25#usize) × Std.Usize) ((Array (Array
    Std.U64 8#usize) 25#usize) × Std.Usize))
  := do
  if idx < total
  then
    let i ← total - idx
    let i1 ← (ok 8#usize : Result Usize)
    let active ← lift (core.cmp.impls.OrdUsize.min i i1)
    let w2_prf := Array.repeat 8#usize 0#u64
    let w2_hash := Array.repeat 8#usize 0#u64
    let w3_id := Array.repeat 8#usize 0#u64
    let (w2_prf1, w2_hash1, w3_id1) ←
      leaves_loop2_loop0 K
        { start := 0#usize, «end» := active } first_key idx w2_prf w2_hash
        w3_id
    let state1 ← NativeShakeWots.fill_prf N state sw skw w0 w1 w2_prf1 w3_id1
    let state2 ← kernel.active state1 active
    let i2 ← params.W - 1#u32
    let state3 ←
      leaves_loop2_loop1 N K
        { start := 0#u32, «end» := i2 } sw w0 w1 state2 active w2_hash1
        w3_id1
    let iter ←
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := active } K
    let (pk1, pos1) ←
      leaves_loop2_loop2 K iter n pk pos state3
    let idx1 ← idx + active
    ok (cont (pk1, pos1, state3, idx1))
  else ok (done (pk, pos))


@[rust_loop]
def leaves_loop2
  (N : Std.Usize) (K : Std.Usize) (first_key : Std.U32) (total : Std.Usize)
  (n : Std.Usize) (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (w0 : Std.U64) (w1 : Std.U64) (pk : Array (Array Std.U64 8#usize) 25#usize)
  (pos : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize)
  (idx : Std.Usize) :
  Result ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
  := do
  loop
    (fun (pk1, pos1, state1, idx1) => leaves_loop2.body
      N K first_key total n sw skw w0 w1 pk1 pos1 state1 idx1)
    (pk, pos, state, idx)


@[rust_loop_body]
def leaves_loop3.body
  (pos : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 8#usize) 25#usize)) (Array (Array Std.U64 8#usize) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some k =>
    let a ← Array.index_usize pk pos
    let i ← Array.index_usize a k
    let i1 ← lift (i ^^^ 31#u64)
    let (a1, index_mut_back) ← Array.index_mut_usize pk pos
    let a2 ← Array.update a1 k i1
    let i2 ← 1#u64 <<< 63#i32
    let pk1 := index_mut_back a2
    let a3 ← Array.index_usize pk1 16#usize
    let i3 ← Array.index_usize a3 k
    let i4 ← lift (i3 ^^^ i2)
    let (a4, index_mut_back1) ← Array.index_mut_usize pk1 16#usize
    let a5 ← Array.update a4 k i4
    let a6 := index_mut_back1 a5
    ok (cont (iter1, a6))


@[rust_loop]
def leaves_loop3
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => leaves_loop3.body pos iter1
      pk1)
    (iter, pk)


def leaves
  {N : Std.Usize} (K : Std.Usize) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (first_key : Std.U32) (addr : address.Adrs) :
  Result (Array (Array Std.U8 N) K)
  := do
  let i ← 2#usize * N
  let len ← i + params.LEN2
  let total ← K * len
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let sw ← NativeVerify.seed_words seed
  let skw ← NativeVerify.seed_words sk
  let base ← NativeVerify.adrs_words addr
  let w0 ← Array.index_usize base 0#usize
  let w1 ← Array.index_usize base 1#usize
  let a := Array.repeat 8#usize 0#u64
  let pk := Array.repeat 25#usize a
  let pk1 ←
    leaves_loop0 { start := 0#usize, «end» := n } sw
      pk
  let a1 := Array.repeat 8#usize w0
  let pk2 ← Array.update pk1 n a1
  let i1 ← n + 1#usize
  let a2 := Array.repeat 8#usize w1
  let a3 ← Array.update pk2 i1 a2
  let pk3 ←
    leaves_loop1 { start := 0#usize, «end» := K }
      first_key n a3
  let a4 := Array.repeat 8#usize 0#u64
  let state := Array.repeat 25#usize a4
  let (pk4, pos) ←
    leaves_loop2 N K first_key total n sw skw w0 w1 pk3
      offset state 0#usize
  let pk5 ←
    leaves_loop3 { start := 0#usize, «end» := K } pk4
      pos
  let pk6 ← kernel.active pk5 K
  core.array.from_fn K
    (leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
    N K) pk6

end slhdsa.Buffered.SmallWots
