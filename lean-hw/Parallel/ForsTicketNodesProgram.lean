import Cachepath.NativeVerify.ActiveHashes
import Cachepath.NativeVerify.ForsFused
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForsTicket
open ShakeBatch NativeVerify
noncomputable section
local instance ticketNodeMachine : Machine := Kldisp.machine
def activeHash := fullActive Kldisp.machine KldispRust.shake256.parallel.available
class Wide where
  run {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)
variable [wide : Wide]

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
  (addr : address.Adrs) (indices : Array Std.U32 3#usize) (level : Std.U32)
  (iter : core.ops.range.Range Std.Usize)
  (out : Array (Array Std.U8 N) 3#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) 3#usize)) (Array (Array Std.U8 N) 3#usize))
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
  (indices : Array Std.U32 3#usize) (level : Std.U32)
  (out : Array (Array Std.U8 N) 3#usize) :
  Result (Array (Array Std.U8 N) 3#usize)
  := do
  loop
    (fun (iter1, out1) =>
      nodes_loop.body sk seed addr
      indices level iter1 out1)
    (iter, out)

def nodes
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 3#usize) (active : Std.Usize)
  (level : Std.U32) :
  Result (Array (Array Std.U8 N) 3#usize)
  := do
  if 3#usize = 8#usize
  then
    if level >= 3#u32
    then
      let a := Array.repeat N 0#u8
      let out := Array.repeat 3#usize a
      nodes_loop
        { start := 0#usize, «end» := active } sk seed addr indices level out
    else
      if level = 0#u32
      then (ForsFused.fused activeHash) sk seed addr indices active
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
        (ActiveHash.pair_active activeHash) seed addresses left right active
  else
    if level = 0#u32
    then (ForsFused.fused activeHash) sk seed addr indices active
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
      (ActiveHash.pair_active activeHash) seed addresses left right active
partial_fixpoint
end
end slhdsa.ParallelForsTicket
