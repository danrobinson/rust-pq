import Cachepath.NativeShakeWots.SignEntry
import Cachepath.NativeVerify.ActiveHashes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Fused
open ShakeBatch NativeVerify

abbrev Subtree := ∀ {N : Usize}, Array U8 N → Array U8 N → U32 → U32 → address.Adrs → Result (Array U8 N)
class Kernel where
  permute : Matrix 8#usize → Result (Matrix 8#usize)
  active : Matrix 8#usize → Usize → Result (Matrix 8#usize)
  subtree : Subtree
  fallback : Subtree
  narrowSign {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Slice U32 → Result (alloc.vec.Vec U8)

@[instance_reducible] def machine (k : Kernel) : Machine := ⟨8#usize,k.permute⟩
variable [kernel : Kernel]
local instance programMachine : Machine := machine kernel
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000

@[reducible]
def xmss_sign_batch.closure_2 (N : Std.Usize) := Std.U32

@[reducible]
def xmss_sign_batch.closure_1 (N : Std.Usize) := Std.U32

@[reducible]
def xmss_sign_batch.closure (N : Std.Usize) := Std.U32

def
  xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : xmss_sign_batch.closure_2 N)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × (xmss_sign_batch.closure_2 N))
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
  xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : xmss_sign_batch.closure_2 N) (i : Std.Usize)
  :
  Result Std.U64
  := do
  let (i1, _) ←
    xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

@[reducible]
def
  xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnOnce
  (xmss_sign_batch.closure_2 N) Std.Usize Std.U64 := {
  call_once :=
    xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

@[reducible]
def
  xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnMut
  (xmss_sign_batch.closure_2 N) Std.Usize Std.U64 := {
  FnOnceInst :=
    xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
    N
  call_mut :=
    xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

def
  xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : xmss_sign_batch.closure_1 N)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × (xmss_sign_batch.closure_1 N))
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
  xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : xmss_sign_batch.closure_1 N) (i : Std.Usize)
  :
  Result Std.U64
  := do
  let (i1, _) ←
    xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

@[reducible]
def
  xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnOnce
  (xmss_sign_batch.closure_1 N) Std.Usize Std.U64 := {
  call_once :=
    xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

@[reducible]
def
  xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnMut
  (xmss_sign_batch.closure_1 N) Std.Usize Std.U64 := {
  FnOnceInst :=
    xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
    N
  call_mut :=
    xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

def
  xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  {N : Std.Usize} (c : xmss_sign_batch.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × (xmss_sign_batch.closure N))
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
  xmss_sign_batch.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  {N : Std.Usize} (c : xmss_sign_batch.closure N) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

@[reducible]
def
  xmss_sign_batch.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnOnce
  (xmss_sign_batch.closure N) Std.Usize Std.U64 := {
  call_once :=
    xmss_sign_batch.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

@[reducible]
def xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  (N : Std.Usize) : core.ops.function.FnMut
  (xmss_sign_batch.closure N) Std.Usize Std.U64 := {
  FnOnceInst :=
    xmss_sign_batch.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
    N
  call_mut :=
    xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

@[rust_loop_body]
def xmss_sign_batch_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (addr : address.Adrs) (iter : core.ops.range.Range Std.U32)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i ← idx >>> j
    let k ← lift (i ^^^ 1#u32)
    let node ← kernel.fallback sk seed k j addr
    let s ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    ok (cont (iter1, sig1))

@[rust_loop]
def xmss_sign_batch_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (idx : Std.U32) (seed : Array Std.U8 N) (addr : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => xmss_sign_batch_loop0.body sk idx seed
      addr iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def xmss_sign_batch_loop1.body
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
def xmss_sign_batch_loop1
  (iter : core.ops.range.Range Std.Usize) (sw : Array Std.U64 4#usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => xmss_sign_batch_loop1.body sw iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def xmss_sign_batch_loop2_loop0.body
  (N : Std.Usize) (sw : Array Std.U64 4#usize) (sig_lane : Std.Usize)
  (w0 : Std.U64) (w1 : Std.U64) (w2_hash : Array Std.U64 8#usize)
  (chain : Std.Usize) (d : Std.U32) (id : Std.U64)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec Std.U8)
    × (Array (Array Std.U64 8#usize) 25#usize)) ((alloc.vec.Vec Std.U8) ×
    (Array (Array Std.U64 8#usize) 25#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done (sig, state))
  | some step =>
    let i ← ShakeBatch.core.num.U32.swap_bytes step
    let i1 ← lift (core.convert.num.FromU64U32.from i)
    let i2 ← i1 <<< 32#i32
    let i3 ← lift (id ||| i2)
    let w3 := Array.repeat 8#usize i3
    let state1 ← NativeShakeWots.refill_short_inplace N state sw w0 w1 w2_hash w3
    let state2 ← kernel.permute state1
    let i4 ← step + 1#u32
    if i4 = d
    then
      let i5 ← chain * N
      let i6 ← chain + 1#usize
      let i7 ← i6 * N
      let (s, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
          Std.U8) sig { start := i5, «end» := i7 }
      let a ← NativeVerify.Wots.extract_lane N state2 0#usize sig_lane
      let s1 ← lift (Array.to_slice a)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let sig1 := index_mut_back s2
      ok (cont (iter1, sig1, state2))
    else ok (cont (iter1, sig, state2))

@[rust_loop]
def xmss_sign_batch_loop2_loop0
  (N : Std.Usize) (iter : core.ops.range.Range Std.U32)
  (sw : Array Std.U64 4#usize) (sig_lane : Std.Usize) (w0 : Std.U64)
  (w1 : Std.U64) (w2_hash : Array Std.U64 8#usize) (sig : alloc.vec.Vec Std.U8)
  (state : Array (Array Std.U64 8#usize) 25#usize) (chain : Std.Usize)
  (d : Std.U32) (id : Std.U64) :
  Result ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 8#usize) 25#usize))
  := do
  loop
    (fun (iter1, sig1, state1) => xmss_sign_batch_loop2_loop0.body
      N sw sig_lane w0 w1 w2_hash chain d id iter1 sig1 state1)
    (iter, sig, state)

@[rust_loop_body]
def xmss_sign_batch_loop2_loop1_loop0.body
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
def xmss_sign_batch_loop2_loop1_loop0
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) (j : Std.Usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => xmss_sign_batch_loop2_loop1_loop0.body pos
      state j iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def xmss_sign_batch_loop2_loop1.body
  (i : Std.Usize) (state : Array (Array Std.U64 8#usize) 25#usize)
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
    let pk1 ←
      xmss_sign_batch_loop2_loop1_loop0
        { start := 0#usize, «end» := i } pk pos state j
    let pos1 ← pos + 1#usize
    if pos1 = 17#usize
    then
      let pk2 ← kernel.permute pk1
      ok (cont (iter1, pk2, 0#usize))
    else ok (cont (iter1, pk1, pos1))

@[rust_loop]
def xmss_sign_batch_loop2_loop1
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result ((Array (Array Std.U64 8#usize) 25#usize) × Std.Usize)
  := do
  loop
    (fun (iter1, pk1, pos1) => xmss_sign_batch_loop2_loop1.body i
      state iter1 pk1 pos1)
    (iter, pk, pos)

@[rust_loop_body]
def xmss_sign_batch_loop2.body
  (N : Std.Usize) (i : Std.Usize) (digits : alloc.vec.Vec Std.U32)
  (n : Std.Usize) (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (sig_lane : Std.Usize) (w0 : Std.U64) (w1 : Std.U64)
  (w2_prf : Array Std.U64 8#usize) (w2_hash : Array Std.U64 8#usize)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8) × (Array (Array Std.U64 8#usize) 25#usize) × Std.Usize × (Array
    (Array Std.U64 8#usize) 25#usize)) ((alloc.vec.Vec Std.U8) × (Array (Array
    Std.U64 8#usize) 25#usize) × Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (sig, pk, pos))
  | some chain =>
    let d ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
        digits chain
    let i1 ← lift (UScalar.cast .U32 chain)
    let i2 ← ShakeBatch.core.num.U32.swap_bytes i1
    let id ← lift (core.convert.num.FromU64U32.from i2)
    let w3_id := Array.repeat 8#usize id
    let state1 ← NativeShakeWots.fill_prf N state sw skw w0 w1 w2_prf w3_id
    let state2 ← kernel.permute state1
    let sig1 ←
      if d = 0#u32
      then
        do
        let i3 ← chain * N
        let i4 ← chain + 1#usize
        let i5 ← i4 * N
        let (s, index_mut_back) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
            Std.U8) sig { start := i3, «end» := i5 }
        let a ← NativeVerify.Wots.extract_lane N state2 0#usize sig_lane
        let s1 ← lift (Array.to_slice a)
        let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
        ok (index_mut_back s2)
      else ok sig
    let i3 ← params.W - 1#u32
    let (sig2, state3) ←
      xmss_sign_batch_loop2_loop0 N
        { start := 0#u32, «end» := i3 } sw sig_lane w0 w1 w2_hash sig1 state2
        chain d id
    let (pk1, pos1) ←
      xmss_sign_batch_loop2_loop1 i
        { start := 0#usize, «end» := n } pk pos state3
    ok (cont (iter1, sig2, pk1, pos1, state3))

@[rust_loop]
def xmss_sign_batch_loop2
  (N : Std.Usize) (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (digits : alloc.vec.Vec Std.U32) (n : Std.Usize) (sw : Array Std.U64 4#usize)
  (skw : Array Std.U64 4#usize) (sig_lane : Std.Usize) (w0 : Std.U64)
  (w1 : Std.U64) (w2_prf : Array Std.U64 8#usize)
  (w2_hash : Array Std.U64 8#usize) (sig : alloc.vec.Vec Std.U8)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize)
  (state : Array (Array Std.U64 8#usize) 25#usize) :
  Result ((alloc.vec.Vec Std.U8) × (Array (Array Std.U64 8#usize) 25#usize) ×
    Std.Usize)
  := do
  loop
    (fun (iter1, sig1, pk1, pos1, state1) =>
      xmss_sign_batch_loop2.body N i digits n sw skw sig_lane w0 w1
      w2_prf w2_hash iter1 sig1 pk1 pos1 state1)
    (iter, sig, pk, pos, state)

@[rust_loop_body]
def xmss_sign_batch_loop3.body
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
def xmss_sign_batch_loop3
  (iter : core.ops.range.Range Std.Usize)
  (pk : Array (Array Std.U64 8#usize) 25#usize) (pos : Std.Usize) :
  Result (Array (Array Std.U64 8#usize) 25#usize)
  := do
  loop
    (fun (iter1, pk1) => xmss_sign_batch_loop3.body pos iter1 pk1)
    (iter, pk)

@[rust_loop_body]
def xmss_sign_batch_loop4.body
  {N : Std.Usize} (base_leaf : Std.U32)
  (nodes : Array (Array Std.U8 N) 8#usize) (tree_adrs : address.Adrs)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.Usize)) × (Array address.Adrs 8#usize) × (Array
    (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N) 8#usize)) ((Array
    address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array
    Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) iter
  match o with
  | none => ok (done (addrs, left, right))
  | some p =>
    let (lane, pr) := p
    let a ← address.Adrs.with_word2 tree_adrs 1#u32
    let i ← base_leaf >>> 1#i32
    let i1 ← lift (UScalar.cast .U32 pr)
    let i2 ← i + i1
    let a1 ← address.Adrs.with_word3 a i2
    let a2 ← Array.update addrs lane a1
    let i3 ← 2#usize * pr
    let a3 ← Array.index_usize nodes i3
    let a4 ← Array.update left lane a3
    let i4 ← i3 + 1#usize
    let a5 ← Array.index_usize nodes i4
    let a6 ← Array.update right lane a5
    ok (cont (iter1, a2, a4, a6))

@[rust_loop]
def xmss_sign_batch_loop4
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (base_leaf : Std.U32) (nodes : Array (Array Std.U8 N) 8#usize)
  (tree_adrs : address.Adrs) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize) ×
    (Array (Array Std.U8 N) 8#usize))
  := do
  loop
    (fun (iter1, addrs1, left1, right1) =>
      xmss_sign_batch_loop4.body base_leaf nodes tree_adrs iter1
      addrs1 left1 right1)
    (iter, addrs, left, right)

@[rust_loop_body]
def xmss_sign_batch_loop5.body
  {N : Std.Usize} (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (addr : address.Adrs) (iter : core.ops.range.Range Std.U32)
  (sig : alloc.vec.Vec Std.U8) (out_pos : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec Std.U8)
    × Std.Usize) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i ← idx >>> j
    let i1 ← lift (i ^^^ 1#u32)
    let node ← kernel.subtree sk seed i1 j addr
    let i2 ← out_pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := out_pos, «end» := i2 }
    let s1 ← lift (Array.to_slice node)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1, i2))

@[rust_loop]
def xmss_sign_batch_loop5
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (idx : Std.U32) (seed : Array Std.U8 N) (addr : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) (out_pos : Std.Usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1, out_pos1) => xmss_sign_batch_loop5.body sk
      idx seed addr iter1 sig1 out_pos1)
    (iter, sig, out_pos)

def xmss_sign_batch
  {N : Std.Usize} (p : params.Params) (m : Array Std.U8 N)
  (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (addr : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let digits ← wots.wots_digits m
  let i ← (ok 8#usize : Result Usize)
  if i != 8#usize
  then
    let a ← address.Adrs.with_type addr address.WOTS_HASH
    let a1 ← address.Adrs.with_keypair a idx
    let s := alloc.vec.Vec.deref digits
    let sig ← kernel.narrowSign sk seed a1 s
    xmss_sign_batch_loop0 { start := 0#u32, «end» := p.hp } sk
      idx seed addr sig
  else
    let len := alloc.vec.Vec.len digits
    let n ← N / 8#usize
    let offset ← n + 4#usize
    let sw ← NativeVerify.seed_words seed
    let skw ← NativeVerify.seed_words sk
    let i1 ← lift (~~~ 7#u32)
    let base_leaf ← lift (idx &&& i1)
    let i2 ← lift (idx &&& 7#u32)
    let sig_lane ← lift (UScalar.cast .Usize i2)
    let base_adrs ← NativeVerify.adrs_words addr
    let w0 ← Array.index_usize base_adrs 0#usize
    let w1 ← Array.index_usize base_adrs 1#usize
    let w2_pk ←
      core.array.from_fn 8#usize
        (xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        N) base_leaf
    let w2_prf ←
      core.array.from_fn 8#usize
        (xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        N) base_leaf
    let w2_hash ←
      core.array.from_fn 8#usize
        (xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        N) base_leaf
    let i3 ← params.Params.xmss_sig_bytes p
    let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i3
    let a := Array.repeat 8#usize 0#u64
    let pk := Array.repeat 25#usize a
    let pk1 ←
      xmss_sign_batch_loop1 { start := 0#usize, «end» := n } sw
        pk
    let a1 := Array.repeat 8#usize w0
    let pk2 ← Array.update pk1 n a1
    let i4 ← n + 1#usize
    let a2 := Array.repeat 8#usize w1
    let pk3 ← Array.update pk2 i4 a2
    let i5 ← n + 2#usize
    let a3 ← Array.update pk3 i5 w2_pk
    let a4 := Array.repeat 8#usize 0#u64
    let state := Array.repeat 25#usize a4
    let (sig1, pk4, pos) ←
      xmss_sign_batch_loop2 N i
        { start := 0#usize, «end» := len } digits n sw skw sig_lane w0 w1
        w2_prf w2_hash sig a3 offset state
    let pk5 ←
      xmss_sign_batch_loop3 { start := 0#usize, «end» := i } pk4
        pos
    let pk6 ← kernel.permute pk5
    let nodes ← NativeVerify.ActiveHash.read_active N pk6 i
    let out_pos ← len * N
    let i6 ← out_pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig1 { start := out_pos, «end» := i6 }
    let i7 ← lift (sig_lane ^^^ 1#usize)
    let a5 ← Array.index_usize nodes i7
    let s1 ← lift (Array.to_slice a5)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let tree_adrs ← address.Adrs.with_type addr address.TREE
    let i8 ← sig_lane >>> 1#i32
    let p1 ← lift (i8 ^^^ 1#usize)
    let i9 ← sig_lane >>> 2#i32
    let h2 ← lift (i9 ^^^ 1#usize)
    let i10 ← 2#usize * h2
    let i11 ← i10 + 1#usize
    let addrs := Array.repeat 8#usize tree_adrs
    let a6 := Array.repeat N 0#u8
    let left := Array.repeat 8#usize a6
    let a7 := Array.repeat N 0#u8
    let right := Array.repeat 8#usize a7
    let s3 ← lift (Array.to_slice (Array.make 3#usize [ p1, i10, i11 ]))
    let i12 ← core.slice.Slice.iter s3
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.Usize) i12
    let sig2 := index_mut_back s2
    let (addrs1, left1, right1) ←
      xmss_sign_batch_loop4 iter base_leaf nodes tree_adrs addrs
        left right
    let lvl1 ← (NativeVerify.ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 3#usize
    let i13 ← i6 + N
    let (s4, index_mut_back1) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig2 { start := i6, «end» := i13 }
    let a8 ← Array.index_usize lvl1 0#usize
    let s5 ← lift (Array.to_slice a8)
    let s6 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s4 s5
    let a9 ← address.Adrs.with_word2 tree_adrs 2#u32
    let i14 ← base_leaf >>> 2#i32
    let i15 ← lift (UScalar.cast .U32 h2)
    let i16 ← i14 + i15
    let a21 ← address.Adrs.with_word3 a9 i16
    let a10 ← Array.index_usize lvl1 1#usize
    let a11 ← Array.index_usize lvl1 2#usize
    let auth2 ← shake.hash.thash_pair seed a21 a10 a11
    let sig3 := index_mut_back1 s6
    let i17 ← i13 + N
    let (s7, index_mut_back2) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig3 { start := i13, «end» := i17 }
    let s8 ← lift (Array.to_slice auth2)
    let s9 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s7 s8
    let sig4 := index_mut_back2 s9
    xmss_sign_batch_loop5 { start := 3#u32, «end» := p.hp } sk
      idx seed addr sig4 i17

end slhdsa.Fused
