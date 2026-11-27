import Cachepath.NativeVerify.ForsSignSecrets
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]
abbrev Nodes := {N : Usize} → Array U8 N → Array U8 N → address.Adrs → Array U32 machine.width →
  U32 → Usize → Result (Rows N)
variable (short : Short) (nodes : Nodes)
@[reducible]
def sign.closure_2 (N : Std.Usize) := Std.U32

def sign.closure_1 (N : Std.Usize) :=
  Std.Usize × Std.Usize × Std.U32 × Slice Std.U32

def
  sign.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : sign.closure_2 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (sign.closure_2 N))
  := do
  let i ← tupled_args >>> c
  let i1 ← lift (i ^^^ 1#u32)
  ok (i1, c)

def
  sign.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : sign.closure_2 N) (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    sign.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def sign.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32 (N :
  Std.Usize) : core.ops.function.FnOnce (sign.closure_2 N)
  Std.U32 Std.U32 := {
  call_once :=
    sign.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def sign.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32 (N :
  Std.Usize) : core.ops.function.FnMut (sign.closure_2 N)
  Std.U32 Std.U32 := {
  FnOnceInst :=
    sign.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32U32 N
  call_mut :=
    sign.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : sign.closure_1 N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (sign.closure_1 N))
  := do
  let (i, i1, i2, s) := c
  let i3 ← i1 - 1#usize
  let i4 ← lift (core.cmp.impls.OrdUsize.min tupled_args i3)
  let tree ← i + i4
  let i5 ← lift (UScalar.cast .U32 tree)
  let i6 ← i5 <<< i2
  let i7 ← Slice.index_usize s tree
  let i8 ← i6 + i7
  ok (i8, c)

def
  sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : sign.closure_1 N) (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 (N
  : Std.Usize) : core.ops.function.FnOnce (sign.closure_1 N)
  Std.Usize Std.U32 := {
  call_once :=
    sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 (N
  : Std.Usize) : core.ops.function.FnMut (sign.closure_1 N)
  Std.Usize Std.U32 := {
  FnOnceInst :=
    sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 N
  call_mut :=
    sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

@[rust_loop_body]
def sign_loop1_loop0.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (stride : Std.Usize) (first : Std.Usize) (active : Std.Usize)
  (indices : Array Std.U32 machine.width) (iter : core.ops.range.Range Std.U32)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let a ←
      core.array.Array.map
        (sign.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices j
    let siblings ←
      nodes sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } a j active
    let sig1 ←
      sign_loop1_loop0_loop0
        { start := 0#usize, «end» := active } stride sig first j siblings
    ok (cont (iter1, sig1))

@[rust_loop]
def sign_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (first : Std.Usize) (active : Std.Usize)
  (indices : Array Std.U32 machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop1_loop0.body nodes sk seed i i1
      i2 i3 i4 i5 stride first active indices iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def sign_loop1.body
  {N : Std.Usize} (selections : Slice Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (k : Std.Usize) (a : Std.U32)
  (stride : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (alloc.vec.Vec Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done sig)
  | some first =>
    let i6 ← k - first
    let active ←
      lift (core.cmp.impls.OrdUsize.min i6 machine.width)
    let indices ←
      core.array.from_fn machine.width
        (sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        N) (first, active, a, selections)
    let sig1 ←
      sign_loop1_loop0 nodes { start := 0#u32, «end» := a } sk
        seed i i1 i2 i3 i4 i5 stride sig first active indices
    ok (cont (iter1, sig1))

@[rust_loop]
def sign_loop1
  {N : Std.Usize}
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (selections : Slice Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (k : Std.Usize) (a : Std.U32) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => sign_loop1.body nodes selections sk seed i
      i1 i2 i3 i4 i5 k a stride iter1 sig1)
    (iter, sig)

def narrow
  {N : Std.Usize} (p : params.Params) (selections : Slice Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let k := Slice.len selections
  let i ← lift (UScalar.cast .Usize p.a)
  let i1 ← i + 1#usize
  let stride ← i1 * N
  let i2 ← k * stride
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i2
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let prf ← address.Adrs.with_keypair a addr.keypair
  let a1 ← address.Adrs.with_type addr address.FORS_TREE
  let tree_adrs ← address.Adrs.with_keypair a1 addr.keypair
  let sig1 ←
    sign_loop0 short selections sk seed k p.a stride sig prf 0#usize
  massert ((machine.width != 8#usize) || (k <= params.K_MAX))
  if machine.width != 8#usize
  then
    let iter ←
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := k } machine.width
    sign_loop1 nodes iter selections sk seed addr.layer addr.tree
      addr.typ addr.keypair addr.word2 addr.word3 k p.a stride sig1
  else fail .panic
end slhdsa.NativeVerify.ForsSign
