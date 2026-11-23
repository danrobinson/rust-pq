import Shakebatch.NodesProgram
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
noncomputable section
variable [machine : Machine]

@[reducible]
def shake.fors_batch.sign.closure_1 (N : Std.Usize) := Std.U32

def shake.fors_batch.sign.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize × params.Params × Slice Std.U32

def
  shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  {N : Std.Usize} (c : shake.fors_batch.sign.closure_1 N)
  (tupled_args : Std.U32) :
  Result (Std.U32 × (shake.fors_batch.sign.closure_1 N))
  := do
  let i ← tupled_args >>> c
  let i1 ← lift (i ^^^ 1#u32)
  ok (i1, c)

def
  shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
  {N : Std.Usize} (c : shake.fors_batch.sign.closure_1 N) (i : Std.U32) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32 (N :
  Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.sign.closure_1 N)
  Std.U32 Std.U32 := {
  call_once :=
    shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once
}

@[reducible]
def shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 (N :
  Std.Usize) : core.ops.function.FnMut (shake.fors_batch.sign.closure_1 N)
  Std.U32 Std.U32 := {
  FnOnceInst :=
    shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32U32 N
  call_mut :=
    shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
}

def
  shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : shake.fors_batch.sign.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (shake.fors_batch.sign.closure N))
  := do
  let (i, i1, p, s) := c
  let i2 ← i1 - 1#usize
  let i3 ← lift (core.cmp.impls.OrdUsize.min tupled_args i2)
  let tree ← i + i3
  let i4 ← lift (UScalar.cast .U32 tree)
  let i5 ← i4 <<< p.a
  let i6 ← Slice.index_usize s tree
  let i7 ← i5 + i6
  ok (i7, c)

def
  shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : shake.fors_batch.sign.closure N) (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 (N :
  Std.Usize) : core.ops.function.FnOnce (shake.fors_batch.sign.closure N)
  Std.Usize Std.U32 := {
  call_once :=
    shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 (N :
  Std.Usize) : core.ops.function.FnMut (shake.fors_batch.sign.closure N)
  Std.Usize Std.U32 := {
  FnOnceInst :=
    shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32 N
  call_mut :=
    shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

@[rust_loop_body]
def shake.fors_batch.sign_loop0_loop0.body
  {N : Std.Usize} (stride : Std.Usize) (first : Std.Usize)
  (secret : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some lane =>
    let i ← first + lane
    let i1 ← i * stride
    let i2 ← i * stride
    let i3 ← i2 + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i1, «end» := i3 }
    let a ← Array.index_usize secret lane
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))

@[rust_loop]
def shake.fors_batch.sign_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (first : Std.Usize)
  (secret : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.fors_batch.sign_loop0_loop0.body stride first
      secret iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def shake.fors_batch.sign_loop0_loop1_loop0.body
  {N : Std.Usize} (stride : Std.Usize) (first : Std.Usize) (j : Std.U32)
  (siblings : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sig)
  | some lane =>
    let i ← first + lane
    let i1 ← i * stride
    let i2 ← lift (UScalar.cast .Usize j)
    let i3 ← i2 + 1#usize
    let i4 ← i3 * N
    let pos ← i1 + i4
    let i5 ← pos + N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := pos, «end» := i5 }
    let a ← Array.index_usize siblings lane
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))

@[rust_loop]
def shake.fors_batch.sign_loop0_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (first : Std.Usize) (j : Std.U32)
  (siblings : Array (Array Std.U8 N) machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.fors_batch.sign_loop0_loop1_loop0.body stride
      first j siblings iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def shake.fors_batch.sign_loop0_loop1.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (stride : Std.Usize) (first : Std.Usize)
  (active : Std.Usize) (indices : Array Std.U32 machine.width)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
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
        (shake.fors_batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32
        N) indices j
    let siblings ← shake.fors_batch.nodes sk seed addr a j
    let sig1 ←
      shake.fors_batch.sign_loop0_loop1_loop0
        { start := 0#usize, «end» := active } stride sig first j siblings
    ok (cont (iter1, sig1))

@[rust_loop]
def shake.fors_batch.sign_loop0_loop1
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (addr : address.Adrs) (stride : Std.Usize)
  (sig : alloc.vec.Vec Std.U8) (first : Std.Usize) (active : Std.Usize)
  (indices : Array Std.U32 machine.width) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.fors_batch.sign_loop0_loop1.body sk seed addr
      stride first active indices iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def shake.fors_batch.sign_loop0.body
  {N : Std.Usize} (i : Std.Usize) (i1 : Std.U32) (i2 : Std.U32) (i3 : Std.U32)
  (i4 : Std.U32) (i5 : Std.U32) (i6 : Std.Usize) (selections : Slice Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs)
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
    let i7 := Slice.len selections
    let i8 ← i7 - first
    let active ←
      lift (core.cmp.impls.OrdUsize.min i8 machine.width)
    let indices ←
      core.array.from_fn machine.width
        (shake.fors_batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        N) (first, active,
        { n := i, h := i1, d := i2, hp := i3, a := i4, k := i5, m := i6 },
        selections)
    let secret ← shake.fors_batch.secrets sk seed addr indices
    let sig1 ←
      shake.fors_batch.sign_loop0_loop0 { start := 0#usize, «end» := active }
        stride sig first secret
    let sig2 ←
      shake.fors_batch.sign_loop0_loop1 { start := 0#u32, «end» := i4 } sk
        seed addr stride sig1 first active indices
    ok (cont (iter1, sig2))

@[rust_loop]
def shake.fors_batch.sign_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (i : Std.Usize) (i1 : Std.U32) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (i6 : Std.Usize) (selections : Slice Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs)
  (stride : Std.Usize) (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.fors_batch.sign_loop0.body i i1 i2 i3 i4 i5 i6
      selections sk seed addr stride iter1 sig1)
    (iter, sig)

def shake.fors_batch.sign
  {N : Std.Usize} (p : params.Params) (selections : Slice Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← lift (UScalar.cast .Usize p.a)
  let i1 ← i + 1#usize
  let stride ← i1 * N
  let i2 := Slice.len selections
  let i3 ← i2 * stride
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i3
  let i4 := Slice.len selections
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := i4 } machine.width
  shake.fors_batch.sign_loop0 iter p.n p.h p.d p.hp p.a p.k p.m selections sk
    seed addr stride sig
end
end slhdsa.ShakeBatch
