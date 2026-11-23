import Shakebatch.Program
import Parent512.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine]

@[reducible]
def shake.fors_batch.secrets.closure (N : Std.Usize) := address.Adrs

@[reducible]
def shake.fors_batch.nodes.closure_2 (N : Std.Usize) := Unit

@[reducible]
def shake.fors_batch.nodes.closure_1 (N : Std.Usize) := Unit

def shake.fors_batch.nodes.closure (N : Std.Usize) := address.Adrs × Std.U32

def
  shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize} (c : shake.fors_batch.secrets.closure N)
  (tupled_args : Std.U32) :
  Result (address.Adrs × (shake.fors_batch.secrets.closure N))
  := do
  let a ← address.Adrs.with_word3 c tupled_args
  ok (a, c)

def
  shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize} (c : shake.fors_batch.secrets.closure N) (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs (N
  : Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.secrets.closure N)
  Std.U32 address.Adrs := {
  call_once :=
    shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs (N
  : Std.Usize) : core.ops.function.FnMut (shake.fors_batch.secrets.closure N)
  Std.U32 address.Adrs := {
  FnOnceInst :=
    shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs N
  call_mut :=
    shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def shake.fors_batch.secrets
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let prf ← address.Adrs.with_keypair a addr.keypair
  let a1 ←
    core.array.Array.map
      (shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs
      N) indices prf
  let a2 := Array.repeat machine.width sk
  shake.batch.short seed a1 a2

def
  shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : shake.fors_batch.nodes.closure_2 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (shake.fors_batch.nodes.closure_2 N))
  := do
  let i ← tupled_args * 2#u32
  let i1 ← i + 1#u32
  ok (i1, c)

def
  shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : shake.fors_batch.nodes.closure_2 N) (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32 (N
  : Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.nodes.closure_2 N)
  Std.U32 Std.U32 := {
  call_once :=
    shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32 (N :
  Std.Usize) : core.ops.function.FnMut (shake.fors_batch.nodes.closure_2 N)
  Std.U32 Std.U32 := {
  FnOnceInst :=
    shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32 N
  call_mut :=
    shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : shake.fors_batch.nodes.closure_1 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (shake.fors_batch.nodes.closure_1 N))
  := do
  let i ← tupled_args * 2#u32
  ok (i, c)

def
  shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : shake.fors_batch.nodes.closure_1 N) (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32 (N
  : Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.nodes.closure_1 N)
  Std.U32 Std.U32 := {
  call_once :=
    shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 (N :
  Std.Usize) : core.ops.function.FnMut (shake.fors_batch.nodes.closure_1 N)
  Std.U32 Std.U32 := {
  FnOnceInst :=
    shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32 N
  call_mut :=
    shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize} (c : shake.fors_batch.nodes.closure N)
  (tupled_args : Std.U32) :
  Result (address.Adrs × (shake.fors_batch.nodes.closure N))
  := do
  let (a, i) := c
  let a1 ← address.Adrs.with_word2 a i
  let a2 ← address.Adrs.with_word3 a1 tupled_args
  ok (a2, c)

def
  shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize} (c : shake.fors_batch.nodes.closure N) (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs (N :
  Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.nodes.closure N)
  Std.U32 address.Adrs := {
  call_once :=
    shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs (N :
  Std.Usize) : core.ops.function.FnMut (shake.fors_batch.nodes.closure N)
  Std.U32 address.Adrs := {
  FnOnceInst :=
    shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnOnceTupleU32Adrs N
  call_mut :=
    shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def shake.fors_batch.nodes
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (level : Std.U32) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let addresses ←
    core.array.Array.map
      (shake.fors_batch.nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs N)
      indices (addr, level)
  if level = 0#u32
  then
    let a ← shake.fors_batch.secrets sk seed addr indices
    shake.batch.short seed addresses a
  else
    let a ←
      core.array.Array.map
        (shake.fors_batch.nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices ()
    let i ← level - 1#u32
    let left ← shake.fors_batch.nodes sk seed addr a i
    let a1 ←
      core.array.Array.map
        (shake.fors_batch.nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices ()
    let right ← shake.fors_batch.nodes sk seed addr a1 i
    shake.batch.pair seed addresses left right
partial_fixpoint
end
end slhdsa.ShakeBatch
