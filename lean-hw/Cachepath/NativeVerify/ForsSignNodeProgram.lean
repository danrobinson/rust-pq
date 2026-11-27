import Cachepath.NativeVerify.ForsSignNarrow
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]
abbrev Leaf := {N : Usize} → Array U8 N → Array U8 N → address.Adrs → Array U32 machine.width → Usize → Result (Rows N)
abbrev Pair := {N : Usize} → Array U8 N → Array address.Adrs machine.width → Rows N → Rows N → Usize → Result (Rows N)
variable (leaf : Leaf) (pair : Pair)
def descend.closure_2 (N : Std.Usize) :=
  address.Adrs × Std.U32

@[reducible]
def descend.closure_1 (N : Std.Usize) := Unit

@[reducible]
def descend.closure (N : Std.Usize) := Unit

def
  descend.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
  {N : Std.Usize} (c : descend.closure_2 N)
  (tupled_args : Std.U32) :
  Result (address.Adrs × (descend.closure_2 N))
  := do
  let (a, i) := c
  let a1 ← address.Adrs.with_word2 a i
  let a2 ← address.Adrs.with_word3 a1 tupled_args
  ok (a2, c)

def
  descend.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
  {N : Std.Usize} (c : descend.closure_2 N)
  (i : Std.U32) :
  Result address.Adrs
  := do
  let (a, _) ←
    descend.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
      c i
  ok a

@[reducible]
def
  descend.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (descend.closure_2 N) Std.U32 address.Adrs := {
  call_once :=
    descend.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs.call_once
}

@[reducible]
def
  descend.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs
  (N : Std.Usize) : core.ops.function.FnMut
  (descend.closure_2 N) Std.U32 address.Adrs := {
  FnOnceInst :=
    descend.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32Adrs
    N
  call_mut :=
    descend.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut
}

def
  descend.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : descend.closure_1 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (descend.closure_1 N))
  := do
  let i ← tupled_args * 2#u32
  let i1 ← i + 1#u32
  ok (i1, c)

def
  descend.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : descend.closure_1 N)
  (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    descend.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def
  descend.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32
  (N : Std.Usize) : core.ops.function.FnOnce
  (descend.closure_1 N) Std.U32 Std.U32 := {
  call_once :=
    descend.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def
  descend.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
  (N : Std.Usize) : core.ops.function.FnMut
  (descend.closure_1 N) Std.U32 Std.U32 := {
  FnOnceInst :=
    descend.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32
    N
  call_mut :=
    descend.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  descend.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : descend.closure N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (descend.closure N))
  := do
  let i ← tupled_args * 2#u32
  ok (i, c)

def
  descend.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : descend.closure N) (i : Std.U32)
  :
  Result Std.U32
  := do
  let (i1, _) ←
    descend.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def
  descend.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32
  (N : Std.Usize) : core.ops.function.FnOnce
  (descend.closure N) Std.U32 Std.U32 := {
  call_once :=
    descend.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def
  descend.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
  (N : Std.Usize) : core.ops.function.FnMut
  (descend.closure N) Std.U32 Std.U32 := {
  FnOnceInst :=
    descend.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32
    N
  call_mut :=
    descend.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def descend
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (level : Std.U32)
  (active : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  if level = 0#u32
  then leaf sk seed addr indices active
  else
    let a ←
      core.array.Array.map
        (descend.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices ()
    let i ← level - 1#u32
    let left ← descend sk seed addr a i active
    let a1 ←
      core.array.Array.map
        (descend.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices ()
    let right ← descend sk seed addr a1 i active
    let addresses ←
      core.array.Array.map
        (descend.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs
        N) indices (addr, level)
    pair seed addresses left right active
partial_fixpoint
end slhdsa.NativeVerify.ForsSign
