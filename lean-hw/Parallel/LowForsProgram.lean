import Cachepath.NativeVerify.ActiveHashes
import Cachepath.NativeVerify.ForsFused
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelLowFors
open ShakeBatch NativeVerify
noncomputable section
class Wide where
  run {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)
class Host (m : Machine) where
  perm : Active m
variable [machine : Machine] [host : Host machine] [wide : Wide]

@[reducible]
def secrets.closure (N : Std.Usize) :=
  address.Adrs

def nodes.closure_2 (N : Std.Usize)
  :=
  address.Adrs × Std.U32

@[reducible]
def nodes.closure_1 (N : Std.Usize)
  :=
Unit

@[reducible]
def nodes.closure (N : Std.Usize) :=
Unit

@[reducible]
def ticket.closure_1 (N : Std.Usize) := Std.U32

def ticket.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize × Std.U32 × alloc.vec.Vec Std.U32

def
  secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize} (c : secrets.closure N)
  (tupled_args : Std.U32) :
  Result (address.Adrs × (secrets.closure
    N))
  := do
  let a ← address.Adrs.with_word3 c tupled_args
  ok (a, c)

def
  secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize} (c : secrets.closure N)
  (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def
  secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (secrets.closure N) Std.U32 address.Adrs
  := {
  call_once :=
    secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def
  secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnMut
  (secrets.closure N) Std.U32 address.Adrs
  := {
  FnOnceInst :=
    secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
    N
  call_mut :=
    secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def secrets
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (active : Std.Usize)
  :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let prf ← address.Adrs.with_keypair a addr.keypair
  let a1 ←
    core.array.Array.map
      (secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs
      N) indices prf
  let a2 := Array.repeat machine.width sk
  (ActiveHash.short_active host.perm) seed a1 a2 active

def
  nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize}
  (c : nodes.closure_2 N)
  (tupled_args : Std.U32) :
  Result (address.Adrs ×
    (nodes.closure_2 N))
  := do
  let (a, i) := c
  let a1 ← address.Adrs.with_word2 a i
  let a2 ← address.Adrs.with_word3 a1 tupled_args
  ok (a2, c)

def
  nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize}
  (c : nodes.closure_2 N)
  (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def
  nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (nodes.closure_2 N) Std.U32
  address.Adrs := {
  call_once :=
    nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def
  nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnMut
  (nodes.closure_2 N) Std.U32
  address.Adrs := {
  FnOnceInst :=
    nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
    N
  call_mut :=
    nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def
  nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize}
  (c : nodes.closure_1 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (nodes.closure_1
    N))
  := do
  let i ← tupled_args * 2#u32
  let i1 ← i + 1#u32
  ok (i1, c)

def
  nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize}
  (c : nodes.closure_1 N)
  (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def
  nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32
  (N : Std.Usize) : core.ops.function.FnOnce
  (nodes.closure_1 N) Std.U32 Std.U32
  := {
  call_once :=
    nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def
  nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
  (N : Std.Usize) : core.ops.function.FnMut
  (nodes.closure_1 N) Std.U32 Std.U32
  := {
  FnOnceInst :=
    nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32
    N
  call_mut :=
    nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize}
  (c : nodes.closure N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (nodes.closure
    N))
  := do
  let i ← tupled_args * 2#u32
  ok (i, c)

def
  nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize}
  (c : nodes.closure N) (i : Std.U32)
  :
  Result Std.U32
  := do
  let (i1, _) ←
    nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def
  nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32
  (N : Std.Usize) : core.ops.function.FnOnce
  (nodes.closure N) Std.U32 Std.U32
  := {
  call_once :=
    nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def
  nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
  (N : Std.Usize) : core.ops.function.FnMut
  (nodes.closure N) Std.U32 Std.U32
  := {
  FnOnceInst :=
    nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32
    N
  call_mut :=
    nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

@[rust_loop_body]
def nodes_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (level : Std.U32)
  (iter : core.ops.range.Range Std.Usize)
  (out : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some lane =>
    let i ← Array.index_usize indices lane
    let a ← wide.run sk seed addr i level
    let a1 ← Array.update out lane a
    ok (cont (iter1, a1))

@[rust_loop]
def nodes_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (addr : address.Adrs)
  (indices : Array Std.U32 machine.width) (level : Std.U32)
  (out : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, out1) =>
      nodes_loop.body sk seed addr
      indices level iter1 out1)
    (iter, out)

def nodes
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (active : Std.Usize)
  (level : Std.U32) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  if machine.width = 8#usize
  then
    if level >= 3#u32
    then
      let a := Array.repeat N 0#u8
      let out := Array.repeat machine.width a
      nodes_loop
        { start := 0#usize, «end» := active } sk seed addr indices level out
    else
      if level = 0#u32
      then (ForsFused.fused host.perm) sk seed addr indices active
      else
        let a ←
          core.array.Array.map
            (nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
            N) indices ()
        let i ← level - 1#u32
        let left ←
          nodes sk seed addr a active
            i
        let a1 ←
          core.array.Array.map
            (nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
            N) indices ()
        let right ←
          nodes sk seed addr a1
            active i
        let addresses ←
          core.array.Array.map
            (nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs
            N) indices (addr, level)
        (ActiveHash.pair_active host.perm) seed addresses left right active
  else
    if level = 0#u32
    then (ForsFused.fused host.perm) sk seed addr indices active
    else
      let a ←
        core.array.Array.map
          (nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
          N) indices ()
      let i ← level - 1#u32
      let left ←
        nodes sk seed addr a active i
      let a1 ←
        core.array.Array.map
          (nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
          N) indices ()
      let right ←
        nodes sk seed addr a1 active
          i
      let addresses ←
        core.array.Array.map
          (nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs
          N) indices (addr, level)
      (ActiveHash.pair_active host.perm) seed addresses left right active
partial_fixpoint

def
  ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : ticket.closure_1 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (ticket.closure_1 N))
  := do
  let i ← tupled_args >>> c
  let i1 ← lift (i ^^^ 1#u32)
  ok (i1, c)

def
  ticket.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : ticket.closure_1 N) (i : Std.U32)
  :
  Result Std.U32
  := do
  let (i1, _) ←
    ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def
  ticket.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32
  (N : Std.Usize) : core.ops.function.FnOnce
  (ticket.closure_1 N) Std.U32 Std.U32 := {
  call_once :=
    ticket.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def
  ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
  (N : Std.Usize) : core.ops.function.FnMut
  (ticket.closure_1 N) Std.U32 Std.U32 := {
  FnOnceInst :=
    ticket.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32
    N
  call_mut :=
    ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : ticket.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (ticket.closure N))
  := do
  let (i, i1, i2, v) := c
  let i3 ← i1 - 1#usize
  let i4 ← lift (core.cmp.impls.OrdUsize.min tupled_args i3)
  let t ← i + i4
  let i5 ← lift (UScalar.cast .U32 t)
  let i6 ← i5 <<< i2
  let i7 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) v t
  let i8 ← i6 + i7
  ok (i8, c)

def
  ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : ticket.closure N) (i : Std.Usize)
  :
  Result Std.U32
  := do
  let (i1, _) ←
    ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def
  ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnOnce
  (ticket.closure N) Std.Usize Std.U32 := {
  call_once :=
    ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def
  ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnMut
  (ticket.closure N) Std.Usize Std.U32 := {
  FnOnceInst :=
    ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    N
  call_mut :=
    ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

@[rust_loop_body]
def ticket_loop0.body
  {N : Std.Usize} (fors_stride : Std.Usize) (first : Std.Usize)
  (secret : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (journal : alloc.vec.Vec (Std.Usize × (Array Std.U8 N))) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Std.Usize × (Array Std.U8 N)))) (alloc.vec.Vec (Std.Usize × (Array
    Std.U8 N))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done journal)
  | some lane =>
    let i ← first + lane
    let i1 ← i * fors_stride
    let a ← Array.index_usize secret lane
    let journal1 ← alloc.vec.Vec.push journal (i1, a)
    ok (cont (iter1, journal1))

@[rust_loop]
def ticket_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (fors_stride : Std.Usize)
  (journal : alloc.vec.Vec (Std.Usize × (Array Std.U8 N))) (first : Std.Usize)
  (secret : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec (Std.Usize × (Array Std.U8 N)))
  := do
  loop
    (fun (iter1, journal1) => ticket_loop0.body
      fors_stride first secret iter1 journal1)
    (iter, journal)

@[rust_loop_body]
def ticket_loop1_loop0.body
  {N : Std.Usize} (fors_stride : Std.Usize) (first : Std.Usize) (j : Std.U32)
  (sibs : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (journal : alloc.vec.Vec (Std.Usize × (Array Std.U8 N))) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Std.Usize × (Array Std.U8 N)))) (alloc.vec.Vec (Std.Usize × (Array
    Std.U8 N))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done journal)
  | some lane =>
    let i ← first + lane
    let i1 ← i * fors_stride
    let i2 ← i1 + 1#usize
    let i3 ← lift (UScalar.cast .Usize j)
    let i4 ← i2 + i3
    let a ← Array.index_usize sibs lane
    let journal1 ← alloc.vec.Vec.push journal (i4, a)
    ok (cont (iter1, journal1))

@[rust_loop]
def ticket_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (fors_stride : Std.Usize)
  (journal : alloc.vec.Vec (Std.Usize × (Array Std.U8 N))) (first : Std.Usize)
  (j : Std.U32) (sibs : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec (Std.Usize × (Array Std.U8 N)))
  := do
  loop
    (fun (iter1, journal1) => ticket_loop1_loop0.body
      fors_stride first j sibs iter1 journal1)
    (iter, journal)

@[rust_loop_body]
def ticket_loop1.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (fors_stride : Std.Usize) (first : Std.Usize)
  (active : Std.Usize) (indices : Array Std.U32 machine.width)
  (iter : core.ops.range.Range Std.U32)
  (journal : alloc.vec.Vec (Std.Usize × (Array Std.U8 N))) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    (Std.Usize × (Array Std.U8 N)))) (alloc.vec.Vec (Std.Usize × (Array
    Std.U8 N))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done journal)
  | some j =>
    let a ←
      core.array.Array.map
        (ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices j
    let sibs ←
      nodes sk seed fors_addr a
        active j
    let journal1 ←
      ticket_loop1_loop0
        { start := 0#usize, «end» := active } fors_stride journal first j
        sibs
    ok (cont (iter1, journal1))

@[rust_loop]
def ticket_loop1
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (fors_addr : address.Adrs) (fors_stride : Std.Usize)
  (journal : alloc.vec.Vec (Std.Usize × (Array Std.U8 N))) (first : Std.Usize)
  (active : Std.Usize) (indices : Array Std.U32 machine.width) :
  Result (alloc.vec.Vec (Std.Usize × (Array Std.U8 N)))
  := do
  loop
    (fun (iter1, journal1) => ticket_loop1.body sk seed
      fors_addr fors_stride first active indices iter1 journal1)
    (iter, journal)

def ticket
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (fors_indices : alloc.vec.Vec Std.U32)
  (a : Std.U32) (first : Std.U16) (active : Std.U8) (low_h : Std.U8)
  (fors_stride : Std.Usize) :
  Result (alloc.vec.Vec (Std.Usize × (Array Std.U8 N)))
  := do
  let first1 ← lift (UScalar.cast .Usize first)
  let active1 ← lift (UScalar.cast .Usize active)
  let indices ←
    core.array.from_fn machine.width
      (ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      N) (first1, active1, a, fors_indices)
  let secret ←
    secrets sk seed fors_addr indices
      active1
  let journal ←
    ticket_loop0
      { start := 0#usize, «end» := active1 } fors_stride (alloc.vec.Vec.new
      (Std.Usize × (Array Std.U8 N))) first1 secret
  let i ← lift (core.convert.num.FromU32U8.from low_h)
  ticket_loop1 { start := 0#u32, «end» := i } sk seed
    fors_addr fors_stride journal first1 active1 indices
end
end slhdsa.ParallelLowFors
