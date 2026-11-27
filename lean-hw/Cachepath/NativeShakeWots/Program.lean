import Cachepath.NativeShakeWots.PackProgram
import Parent512.FunsExternal
import Cachepath.NativeVerify.WotsRecover
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeShakeWots
open ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine] [NativeVerify.Wots.Dispatch machine] [stream : Stream]
@[reducible]
def keygen.closure_1 (N : Std.Usize) := Std.U64

def keygen.closure (N : Std.Usize) := Std.Usize × Std.Usize

def sign.closure (N : Std.Usize) := Std.Usize × Std.Usize

def keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
  {N : Std.Usize} (c : keygen.closure_1 N) (tupled_args : Std.U64)
  :
  Result (Std.U64 × (keygen.closure_1 N))
  := do
  let i ← lift (tupled_args ||| c)
  ok (i, c)

def
  keygen.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once
  {N : Std.Usize} (c : keygen.closure_1 N) (i : Std.U64) :
  Result Std.U64
  := do
  let (i1, _) ←
    keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
      c i
  ok i1

@[reducible]
def keygen.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64 (N :
  Std.Usize) : core.ops.function.FnOnce (keygen.closure_1 N)
  Std.U64 Std.U64 := {
  call_once :=
    keygen.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once
}

@[reducible]
def keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64 (N :
  Std.Usize) : core.ops.function.FnMut (keygen.closure_1 N) Std.U64
  Std.U64 := {
  FnOnceInst :=
    keygen.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64 N
  call_mut :=
    keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut
}

def keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : keygen.closure N) (tupled_args : Std.Usize)
  :
  Result (Std.U64 × (keygen.closure N))
  := do
  let (i, i1) := c
  let i2 ← i1 - 1#usize
  let i3 ← lift (core.cmp.impls.OrdUsize.min tupled_args i2)
  let i4 ← i + i3
  let i5 ← lift (UScalar.cast .U32 i4)
  let i6 ← ShakeBatch.core.num.U32.swap_bytes i5
  let i7 ← lift (core.convert.num.FromU64U32.from i6)
  ok (i7, c)

def
  keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : keygen.closure N) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

@[reducible]
def keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64 (N :
  Std.Usize) : core.ops.function.FnOnce (keygen.closure N)
  Std.Usize Std.U64 := {
  call_once :=
    keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

@[reducible]
def keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 (N :
  Std.Usize) : core.ops.function.FnMut (keygen.closure N) Std.Usize
  Std.U64 := {
  FnOnceInst :=
    keygen.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64 N
  call_mut :=
    keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

@[rust_loop_body]
def keygen_loop0_loop0.body
  (N : Std.Usize) (sw : Array Std.U64 4#usize)
  (aw_hash : Array Std.U64 4#usize) (w2_hash : Array Std.U64 machine.width)
  (active : Std.Usize) (ids : Array Std.U64 machine.width)
  (iter : core.ops.range.Range Std.U32)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Array Std.U64
    machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
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
        (keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64 N)
        ids step_hi
    let i2 ← Array.index_usize aw_hash 0#usize
    let i3 ← Array.index_usize aw_hash 1#usize
    let state1 ← refill_short_inplace N state sw i2 i3 w2_hash w3
    let state2 ← NativeVerify.Wots.Dispatch.permute state1 active
    ok (cont (iter1, state2))

@[rust_loop]
def keygen_loop0_loop0
  (N : Std.Usize) (iter : core.ops.range.Range Std.U32)
  (sw : Array Std.U64 4#usize) (aw_hash : Array Std.U64 4#usize)
  (w2_hash : Array Std.U64 machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (active : Std.Usize)
  (ids : Array Std.U64 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => keygen_loop0_loop0.body N sw aw_hash
      w2_hash active ids iter1 state1)
    (iter, state)

@[rust_loop_body]
def keygen_loop0_loop1.body
  (N : Std.Usize) (state : Array (Array Std.U64 machine.width) 25#usize)
  (iter : core.ops.range.Range Std.Usize) (pk : stream.State) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × stream.State)
    stream.State)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some lane =>
    let a ← NativeVerify.Wots.extract_lane N state 0#usize lane
    let s ← lift (Array.to_slice a)
    let pk1 ← stream.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def keygen_loop0_loop1
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => keygen_loop0_loop1.body N state iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def keygen_loop0.body
  (N : Std.Usize) (i : Std.Usize) (len : Std.Usize)
  (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (aw_prf : Array Std.U64 4#usize) (aw_hash : Array Std.U64 4#usize)
  (w2_prf : Array Std.U64 machine.width) (w2_hash : Array Std.U64 machine.width)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (state : Array (Array Std.U64 machine.width) 25#usize) (pk : stream.State) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Array (Array Std.U64 machine.width) 25#usize) × stream.State)
    stream.State)
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done pk)
  | some i1 =>
    let i2 ← len - i1
    let active ← lift (core.cmp.impls.OrdUsize.min i2 i)
    let ids ←
      core.array.from_fn machine.width
        (keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N)
        (i1, active)
    let i3 ← Array.index_usize aw_prf 0#usize
    let i4 ← Array.index_usize aw_prf 1#usize
    let state1 ← fill_prf N state sw skw i3 i4 w2_prf ids
    let state2 ← NativeVerify.Wots.Dispatch.permute state1 active
    let i5 ← params.W - 1#u32
    let state3 ←
      keygen_loop0_loop0 N { start := 0#u32, «end» := i5 } sw
        aw_hash w2_hash state2 active ids
    let pk1 ←
      keygen_loop0_loop1 N { start := 0#usize, «end» := active }
        state3 pk
    ok (cont (iter1, state3, pk1))

@[rust_loop]
def keygen_loop0
  (N : Std.Usize) (i : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (len : Std.Usize) (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (aw_prf : Array Std.U64 4#usize) (aw_hash : Array Std.U64 4#usize)
  (w2_prf : Array Std.U64 machine.width) (w2_hash : Array Std.U64 machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, state1, pk1) => keygen_loop0.body N i len sw skw
      aw_prf aw_hash w2_prf w2_hash iter1 state1 pk1)
    (iter, state, pk)

def keygen
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← 2#usize * N
  let len ← i + params.LEN2
  let sw ← NativeVerify.seed_words seed
  let skw ← NativeVerify.seed_words sk
  let a ← address.Adrs.with_type addr address.WOTS_PRF
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let aw_prf ← NativeVerify.adrs_words a1
  let a2 ← address.Adrs.with_type addr address.WOTS_HASH
  let a3 ← address.Adrs.with_keypair a2 addr.keypair
  let aw_hash ← NativeVerify.adrs_words a3
  let i1 ← Array.index_usize aw_prf 2#usize
  let w2_prf := Array.repeat machine.width i1
  let i2 ← Array.index_usize aw_hash 2#usize
  let w2_hash := Array.repeat machine.width i2
  let a4 := Array.repeat machine.width 0#u64
  let state := Array.repeat 25#usize a4
  let a5 ← address.Adrs.with_type addr address.WOTS_PK
  let a6 ← address.Adrs.with_keypair a5 addr.keypair
  let pk ← stream.start seed a6
  let i3 ← (ok machine.width : Result Usize)
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := len } i3
  let pk1 ←
    keygen_loop0 N i3 iter len sw skw aw_prf aw_hash w2_prf w2_hash
      state pk
  stream.digest N pk1

def sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : sign.closure N) (tupled_args : Std.Usize) :
  Result (Std.U64 × (sign.closure N))
  := do
  let (i, i1) := c
  let i2 ← i1 - 1#usize
  let i3 ← lift (core.cmp.impls.OrdUsize.min tupled_args i2)
  let i4 ← i + i3
  let i5 ← lift (UScalar.cast .U32 i4)
  let i6 ← ShakeBatch.core.num.U32.swap_bytes i5
  let i7 ← lift (core.convert.num.FromU64U32.from i6)
  ok (i7, c)

def sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : sign.closure N) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut c
      i
  ok i1

@[reducible]
def sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64 (N :
  Std.Usize) : core.ops.function.FnOnce (sign.closure N) Std.Usize
  Std.U64 := {
  call_once :=
    sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

@[reducible]
def sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 (N :
  Std.Usize) : core.ops.function.FnMut (sign.closure N) Std.Usize
  Std.U64 := {
  FnOnceInst :=
    sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64 N
  call_mut :=
    sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

@[rust_loop_body]
def sign_loop0_loop0_loop0.body
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (id : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 4#usize) 67#usize)) (Array (Array Std.U64 4#usize) 67#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done secrets_words)
  | some j =>
    let a ← Array.index_usize state j
    let i ← Array.index_usize a lane
    let (a1, index_mut_back) ← Array.index_mut_usize secrets_words id
    let a2 ← Array.update a1 j i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def sign_loop0_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (id : Std.Usize) :
  Result (Array (Array Std.U64 4#usize) 67#usize)
  := do
  loop
    (fun (iter1, secrets_words1) => sign_loop0_loop0_loop0.body
      state lane id iter1 secrets_words1)
    (iter, secrets_words)

@[rust_loop_body]
def sign_loop0_loop0.body
  (N : Std.Usize) (digits : Slice Std.U32) (n : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (i : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8) × (Array (Array Std.U64 4#usize) 67#usize)) ((alloc.vec.Vec
    Std.U8) × (Array (Array Std.U64 4#usize) 67#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (sig, secrets_words))
  | some lane =>
    let id ← i + lane
    let i1 ← Slice.index_usize digits id
    if i1 = 0#u32
    then
      let i2 ← id * N
      let i3 ← id + 1#usize
      let i4 ← i3 * N
      let (s, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
          Std.U8) sig { start := i2, «end» := i4 }
      let a ← NativeVerify.Wots.extract_lane N state 0#usize lane
      let s1 ← lift (Array.to_slice a)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let sig1 := index_mut_back s2
      ok (cont (iter1, sig1, secrets_words))
    else
      let secrets_words1 ←
        sign_loop0_loop0_loop0 { start := 0#usize, «end» := n }
          secrets_words state lane id
      ok (cont (iter1, sig, secrets_words1))

@[rust_loop]
def sign_loop0_loop0
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (digits : Slice Std.U32) (n : Std.Usize) (sig : alloc.vec.Vec Std.U8)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (i : Std.Usize) :
  Result ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 4#usize) 67#usize))
  := do
  loop
    (fun (iter1, sig1, secrets_words1) => sign_loop0_loop0.body N
      digits n state i iter1 sig1 secrets_words1)
    (iter, sig, secrets_words)

@[rust_loop_body]
def sign_loop0.body
  (N : Std.Usize) (i : Std.Usize) (digits : Slice Std.U32) (len : Std.Usize)
  (n : Std.Usize) (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (aw_prf : Array Std.U64 4#usize) (w2_prf : Array Std.U64 machine.width)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (sig : alloc.vec.Vec Std.U8)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (alloc.vec.Vec Std.U8) × (Array (Array Std.U64 4#usize)
    67#usize) × (Array (Array Std.U64 machine.width) 25#usize)) ((alloc.vec.Vec
    Std.U8) × (Array (Array Std.U64 4#usize) 67#usize) × (Array (Array
    Std.U64 machine.width) 25#usize)))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (sig, secrets_words, state))
  | some i1 =>
    let i2 ← len - i1
    let active ← lift (core.cmp.impls.OrdUsize.min i2 i)
    let ids ←
      core.array.from_fn machine.width
        (sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N)
        (i1, active)
    let i3 ← Array.index_usize aw_prf 0#usize
    let i4 ← Array.index_usize aw_prf 1#usize
    let state1 ← fill_prf N state sw skw i3 i4 w2_prf ids
    let state2 ← NativeVerify.Wots.Dispatch.permute state1 active
    let (sig1, secrets_words1) ←
      sign_loop0_loop0 N { start := 0#usize, «end» := active }
        digits n sig secrets_words state2 i1
    ok (cont (iter1, sig1, secrets_words1, state2))

@[rust_loop]
def sign_loop0
  (N : Std.Usize) (i : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (digits : Slice Std.U32) (len : Std.Usize) (n : Std.Usize)
  (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (aw_prf : Array Std.U64 4#usize) (w2_prf : Array Std.U64 machine.width)
  (sig : alloc.vec.Vec Std.U8)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 4#usize) 67#usize) ×
    (Array (Array Std.U64 machine.width) 25#usize))
  := do
  loop
    (fun (iter1, sig1, secrets_words1, state1) => sign_loop0.body N
      i digits len n sw skw aw_prf w2_prf iter1 sig1 secrets_words1 state1)
    (iter, sig, secrets_words, state)

@[rust_loop_body]
def sign_loop1.body
  (digits : Slice Std.U32)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (order : Array Std.Usize 67#usize) (iter : core.ops.range.Range Std.Usize)
  (next : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (lane_end : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize × (Array
    Std.Usize machine.width) × (Array Std.U32 machine.width) × (Array Std.U32 machine.width) ×
    (Array (Array Std.U64 4#usize) machine.width)) (Std.Usize × (Array Std.Usize
    machine.width) × (Array Std.U32 machine.width) × (Array Std.U32 machine.width) × (Array
    (Array Std.U64 4#usize) machine.width)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (next, lane_id, lane_step, lane_end, lane_val))
  | some lane =>
    let id ← Array.index_usize order next
    let next1 ← next + 1#usize
    let a ← Array.update lane_id lane id
    let a1 ← Array.update lane_step lane 0#u32
    let i ← Slice.index_usize digits id
    let a2 ← Array.update lane_end lane i
    let a3 ← Array.index_usize secrets_words id
    let a4 ← Array.update lane_val lane a3
    ok (cont (iter1, next1, a, a1, a2, a4))

@[rust_loop]
def sign_loop1
  (iter : core.ops.range.Range Std.Usize) (digits : Slice Std.U32)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (order : Array Std.Usize 67#usize) (next : Std.Usize)
  (lane_id : Array Std.Usize machine.width) (lane_step : Array Std.U32 machine.width)
  (lane_end : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (Std.Usize × (Array Std.Usize machine.width) × (Array Std.U32 machine.width) ×
    (Array Std.U32 machine.width) × (Array (Array Std.U64 4#usize) machine.width))
  := do
  loop
    (fun (iter1, next1, lane_id1, lane_step1, lane_end1, lane_val1) =>
      sign_loop1.body digits secrets_words order iter1 next1
      lane_id1 lane_step1 lane_end1 lane_val1)
    (iter, next, lane_id, lane_step, lane_end, lane_val)

@[rust_loop_body]
def sign_loop2_loop0_loop0.body
  (offset : Std.Usize) (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let a ← Array.index_usize lane_val lane
    let i ← Array.index_usize a j
    let i1 ← offset + j
    let (a1, index_mut_back) ← Array.index_mut_usize state i1
    let a2 ← Array.update a1 lane i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def sign_loop2_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (j : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => sign_loop2_loop0_loop0.body offset
      lane_val j iter1 state1)
    (iter, state)

@[rust_loop_body]
def sign_loop2_loop0.body
  (offset : Std.Usize) (sw : Array Std.U64 4#usize) (active : Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some j =>
    let i ← Array.index_usize sw j
    let a := Array.repeat machine.width i
    let a1 ← Array.update state j a
    let state1 ←
      sign_loop2_loop0_loop0
        { start := 0#usize, «end» := active } offset a1 lane_val j
    ok (cont (iter1, state1))

@[rust_loop]
def sign_loop2_loop0
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (sw : Array Std.U64 4#usize) (state : Array (Array Std.U64 machine.width) 25#usize)
  (active : Std.Usize) (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => sign_loop2_loop0.body offset sw active
      lane_val iter1 state1)
    (iter, state)

@[rust_loop_body]
def sign_loop2_loop1.body
  (n : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let i ← Array.index_usize lane_id lane
    let i1 ← lift (UScalar.cast .U32 i)
    let i2 ← ShakeBatch.core.num.U32.swap_bytes i1
    let i3 ← lift (core.convert.num.FromU64U32.from i2)
    let i4 ← Array.index_usize lane_step lane
    let i5 ← ShakeBatch.core.num.U32.swap_bytes i4
    let i6 ← lift (core.convert.num.FromU64U32.from i5)
    let i7 ← i6 <<< 32#i32
    let i8 ← n + 3#usize
    let (a, index_mut_back) ← Array.index_mut_usize state i8
    let i9 ← lift (i3 ||| i7)
    let a1 ← Array.update a lane i9
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

@[rust_loop]
def sign_loop2_loop1
  (iter : core.ops.range.Range Std.Usize) (n : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (lane_id : Array Std.Usize machine.width) (lane_step : Array Std.U32 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => sign_loop2_loop1.body n lane_id
      lane_step iter1 state1)
    (iter, state)

@[rust_loop_body]
def sign_loop2_loop2.body
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result (ControlFlow ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width))) ((core.slice.iter.IterMut
    (Array Std.U64 machine.width)) × (core.slice.iter.IterMut (Array Std.U64
    machine.width) → core.slice.iter.IterMut (Array Std.U64 machine.width))))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some _ =>
    let w := Array.repeat machine.width 0#u64
    ok (cont (iter1, fun im => let im1 := next_back im (some w)
                               back im1))

@[rust_loop]
def sign_loop2_loop2
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => sign_loop2_loop2.body iter1 back1)
    (iter, back)

@[rust_loop_body]
def sign_loop2_loop3_loop0.body
  (active : Std.Usize) (lane : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some j =>
    let a ← Array.index_usize state j
    let i ← Array.index_usize a active
    let (a1, index_mut_back) ← Array.index_mut_usize state j
    let a2 ← Array.update a1 lane i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def sign_loop2_loop3_loop0
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (active : Std.Usize)
  (lane : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => sign_loop2_loop3_loop0.body active lane
      iter1 state1)
    (iter, state)

@[rust_loop_body]
def sign_loop2_loop3_loop1.body
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 4#usize) machine.width)) (Array (Array Std.U64 4#usize) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done lane_val)
  | some j =>
    let a ← Array.index_usize state j
    let i ← Array.index_usize a lane
    let (a1, index_mut_back) ← Array.index_mut_usize lane_val lane
    let a2 ← Array.update a1 j i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def sign_loop2_loop3_loop1
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (lane : Std.Usize) :
  Result (Array (Array Std.U64 4#usize) machine.width)
  := do
  loop
    (fun (iter1, lane_val1) => sign_loop2_loop3_loop1.body state
      lane iter1 lane_val1)
    (iter, lane_val)

@[rust_loop_body]
def sign_loop2_loop3.body
  (N : Std.Usize) (digits : Slice Std.U32) (n : Std.Usize)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (state : Array (Array Std.U64 machine.width) 25#usize)
  (next : Std.Usize) (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (lane_end : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (lane : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 machine.width)
    25#usize) × Std.Usize × Std.Usize × (Array Std.Usize machine.width) × (Array
    Std.U32 machine.width) × (Array Std.U32 machine.width) × (Array (Array Std.U64
    4#usize) machine.width) × Std.Usize) ((alloc.vec.Vec Std.U8) × (Array (Array
    Std.U64 machine.width) 25#usize) × Std.Usize × Std.Usize × (Array Std.Usize
    machine.width) × (Array Std.U32 machine.width) × (Array Std.U32 machine.width) × (Array
    (Array Std.U64 4#usize) machine.width)))
  := do
  if lane < active
  then
    let i ← Array.index_usize lane_step lane
    let i1 ← i + 1#u32
    let lane_step1 ← Array.update lane_step lane i1
    let i2 ← Array.index_usize lane_step1 lane
    let i3 ← Array.index_usize lane_end lane
    if i2 = i3
    then
      let id ← Array.index_usize lane_id lane
      let i4 ← id * N
      let i5 ← id + 1#usize
      let i6 ← i5 * N
      let (s, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
          Std.U8) sig { start := i4, «end» := i6 }
      let a ← NativeVerify.Wots.extract_lane N state 0#usize lane
      let s1 ← lift (Array.to_slice a)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      if next < total
      then
        let nid ← Array.index_usize order next
        let next1 ← next + 1#usize
        let a1 ← Array.update lane_id lane nid
        let a2 ← Array.update lane_step1 lane 0#u32
        let i7 ← Slice.index_usize digits nid
        let a3 ← Array.update lane_end lane i7
        let a4 ← Array.index_usize secrets_words nid
        let a5 ← Array.update lane_val lane a4
        let lane1 ← lane + 1#usize
        let sig1 := index_mut_back s2
        ok (cont (sig1, state, next1, active, a1, a2, a3, a5, lane1))
      else
        let active1 ← active - 1#usize
        if lane < active1
        then
          let i7 ← Array.index_usize lane_id active1
          let a1 ← Array.update lane_id lane i7
          let i8 ← Array.index_usize lane_step1 active1
          let a2 ← Array.update lane_step1 lane i8
          let i9 ← Array.index_usize lane_end active1
          let a3 ← Array.update lane_end lane i9
          let sig1 := index_mut_back s2
          let state1 ←
            sign_loop2_loop3_loop0
              { start := 0#usize, «end» := n } state active1 lane
          ok (cont (sig1, state1, next, active1, a1, a2, a3, lane_val, lane))
        else
          let sig1 := index_mut_back s2
          ok (cont (sig1, state, next, active1, lane_id, lane_step1, lane_end,
            lane_val, lane))
    else
      let lane_val1 ←
        sign_loop2_loop3_loop1 { start := 0#usize, «end» := n }
          state lane_val lane
      let lane1 ← lane + 1#usize
      ok (cont (sig, state, next, active, lane_id, lane_step1, lane_end,
        lane_val1, lane1))
  else
    ok (done (sig, state, next, active, lane_id, lane_step, lane_end,
      lane_val))

@[rust_loop]
def sign_loop2_loop3
  (N : Std.Usize) (digits : Slice Std.U32) (n : Std.Usize)
  (sig : alloc.vec.Vec Std.U8)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize) (next : Std.Usize)
  (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (lane_end : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (lane : Std.Usize) :
  Result ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 machine.width) 25#usize) ×
    Std.Usize × Std.Usize × (Array Std.Usize machine.width) × (Array Std.U32
    machine.width) × (Array Std.U32 machine.width) × (Array (Array Std.U64 4#usize)
    machine.width))
  := do
  loop
    (fun (sig1, state1, next1, active1, lane_id1, lane_step1, lane_end1,
      lane_val1, lane1) => sign_loop2_loop3.body N digits n
      secrets_words order total sig1 state1 next1 active1 lane_id1 lane_step1
      lane_end1 lane_val1 lane1)
    (sig, state, next, active, lane_id, lane_step, lane_end, lane_val, lane)

@[rust_loop_body]
def sign_loop2.body
  (N : Std.Usize) (digits : Slice Std.U32) (n : Std.Usize) (offset : Std.Usize)
  (sw : Array Std.U64 4#usize) (aw_hash : Array Std.U64 4#usize)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize) (pad : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (state : Array (Array Std.U64 machine.width) 25#usize)
  (next : Std.Usize) (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (lane_end : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 machine.width)
    25#usize) × Std.Usize × Std.Usize × (Array Std.Usize machine.width) × (Array
    Std.U32 machine.width) × (Array Std.U32 machine.width) × (Array (Array Std.U64
    4#usize) machine.width)) (alloc.vec.Vec Std.U8))
  := do
  if active > 0#usize
  then
    let state1 ←
      sign_loop2_loop0 { start := 0#usize, «end» := n } offset sw
        state active lane_val
    let i ← Array.index_usize aw_hash 0#usize
    let a := Array.repeat machine.width i
    let state2 ← Array.update state1 n a
    let i1 ← Array.index_usize aw_hash 1#usize
    let i2 ← n + 1#usize
    let a1 := Array.repeat machine.width i1
    let state3 ← Array.update state2 i2 a1
    let i3 ← Array.index_usize aw_hash 2#usize
    let i4 ← n + 2#usize
    let a2 := Array.repeat machine.width i3
    let a3 ← Array.update state3 i4 a2
    let state4 ←
      sign_loop2_loop1 { start := 0#usize, «end» := active } n a3
        lane_id lane_step
    let a4 := Array.repeat machine.width 31#u64
    let state5 ← Array.update state4 pad a4
    let i5 ← pad + 1#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
        state5 { start := i5, «end» := 25#usize }
    let (iter, into_iter_back) ←
      core.slice.Slice.iter_mut s
    let (im, back) ← sign_loop2_loop2 iter (fun im1 => im1)
    let i6 ← 1#u64 <<< 63#i32
    let im1 := back im
    let s1 := into_iter_back im1
    let state6 := index_mut_back s1
    let a5 := Array.repeat machine.width i6
    let state7 ← Array.update state6 16#usize a5
    let state8 ← NativeVerify.Wots.Dispatch.permute state7 active
    let (sig1, state9, next1, active1, lane_id1, lane_step1, lane_end1,
      lane_val1) ←
      sign_loop2_loop3 N digits n sig secrets_words state8 order
        total next active lane_id lane_step lane_end lane_val 0#usize
    ok (cont (sig1, state9, next1, active1, lane_id1, lane_step1, lane_end1,
      lane_val1))
  else ok (done sig)

@[rust_loop]
def sign_loop2
  (N : Std.Usize) (digits : Slice Std.U32) (n : Std.Usize) (offset : Std.Usize)
  (sw : Array Std.U64 4#usize) (aw_hash : Array Std.U64 4#usize)
  (sig : alloc.vec.Vec Std.U8)
  (secrets_words : Array (Array Std.U64 4#usize) 67#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize) (next : Std.Usize)
  (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (lane_end : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (pad : Std.Usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, state1, next1, active1, lane_id1, lane_step1, lane_end1,
      lane_val1) => sign_loop2.body N digits n offset sw aw_hash
      secrets_words order total pad sig1 state1 next1 active1 lane_id1
      lane_step1 lane_end1 lane_val1)
    (sig, state, next, active, lane_id, lane_step, lane_end, lane_val)

def sign
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (digits : Slice Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let len := Slice.len digits
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let sw ← NativeVerify.seed_words seed
  let skw ← NativeVerify.seed_words sk
  let a ← address.Adrs.with_type addr address.WOTS_PRF
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let aw_prf ← NativeVerify.adrs_words a1
  let a2 ← address.Adrs.with_type addr address.WOTS_HASH
  let a3 ← address.Adrs.with_keypair a2 addr.keypair
  let aw_hash ← NativeVerify.adrs_words a3
  let i ← Array.index_usize aw_prf 2#usize
  let w2_prf := Array.repeat machine.width i
  let i1 ← N * len
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i1
  let a4 := Array.repeat 4#usize 0#u64
  let secrets_words := Array.repeat 67#usize a4
  let a5 := Array.repeat machine.width 0#u64
  let state := Array.repeat 25#usize a5
  let i2 ← (ok machine.width : Result Usize)
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := len } i2
  let (sig1, secrets_words1, state1) ←
    sign_loop0 N i2 iter digits len n sw skw aw_prf w2_prf sig
      secrets_words state
  let (order, total) ← ShakeoptSort.shake.batch.sort_descending digits
  let active ← lift (core.cmp.impls.OrdUsize.min total i2)
  let lane_id := Array.repeat machine.width 0#usize
  let lane_step := Array.repeat machine.width 0#u32
  let lane_end := Array.repeat machine.width 0#u32
  let a6 := Array.repeat 4#usize 0#u64
  let lane_val := Array.repeat machine.width a6
  let (next, lane_id1, lane_step1, lane_end1, lane_val1) ←
    sign_loop1 { start := 0#usize, «end» := active } digits
      secrets_words1 order 0#usize lane_id lane_step lane_end lane_val
  let pad ← offset + n
  sign_loop2 N digits n offset sw aw_hash sig1 secrets_words1
    state1 order total next active lane_id1 lane_step1 lane_end1 lane_val1 pad
end
end slhdsa.NativeShakeWots
