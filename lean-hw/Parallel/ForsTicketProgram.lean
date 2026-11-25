import Parallel.ForsTicketNodesProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForsTicket
noncomputable section
variable [wide : Wide]

def direct_ticket.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize × Std.U32 × Std.U32 × alloc.vec.Vec Std.U32

def split_ticket.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize × Std.U32 × Std.U32 × alloc.vec.Vec Std.U32 ×
  Std.U32 × Std.U32

def
  direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : direct_ticket.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (direct_ticket.closure N))
  := do
  let (i, i1, i2, i3, v) := c
  let i4 ← i1 - 1#usize
  let i5 ← lift (core.cmp.impls.OrdUsize.min tupled_args i4)
  let t ← i + i5
  let i6 ← lift (UScalar.cast .U32 t)
  let i7 ← i2 - i3
  let i8 ← i6 <<< i7
  let i9 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) v t
  let i10 ← i9 >>> i3
  let i11 ← lift (i10 ^^^ 1#u32)
  let i12 ← i8 + i11
  ok (i12, c)

def
  direct_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : direct_ticket.closure N)
  (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def
  direct_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnOnce
  (direct_ticket.closure N) Std.Usize Std.U32 := {
  call_once :=
    direct_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def
  direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnMut
  (direct_ticket.closure N) Std.Usize Std.U32 := {
  FnOnceInst :=
    direct_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    N
  call_mut :=
    direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

@[rust_loop_body]
def direct_ticket_loop.body
  {N : Std.Usize} (fors_stride : Std.Usize) (first : Std.Usize) (j : Std.U32)
  (sibs : Array (Array Std.U8 N) 3#usize)
  (iter : core.ops.range.Range Std.Usize)
  (writes : Array (Std.Usize × (Array Std.U8 N)) 3#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Std.Usize ×
    (Array Std.U8 N)) 3#usize)) (Array (Std.Usize × (Array Std.U8 N))
    3#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done writes)
  | some lane =>
    let i ← first + lane
    let i1 ← i * fors_stride
    let i2 ← i1 + 1#usize
    let i3 ← lift (UScalar.cast .Usize j)
    let i4 ← i2 + i3
    let a ← Array.index_usize sibs lane
    let a1 ← Array.update writes lane (i4, a)
    ok (cont (iter1, a1))

@[rust_loop]
def direct_ticket_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (fors_stride : Std.Usize) (first : Std.Usize) (j : Std.U32)
  (sibs : Array (Array Std.U8 N) 3#usize)
  (writes : Array (Std.Usize × (Array Std.U8 N)) 3#usize) :
  Result (Array (Std.Usize × (Array Std.U8 N)) 3#usize)
  := do
  loop
    (fun (iter1, writes1) => direct_ticket_loop.body
      fors_stride first j sibs iter1 writes1)
    (iter, writes)

def direct_ticket
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (fors_indices : alloc.vec.Vec Std.U32)
  (a : Std.U32) (first : Std.U16) (active : Std.U8) (height : Std.U8)
  (fors_stride : Std.Usize) :
  Result (Array (Std.Usize × (Array Std.U8 N)) 3#usize)
  := do
  let first1 ← lift (UScalar.cast .Usize first)
  let active1 ← lift (UScalar.cast .Usize active)
  let j ← lift (core.convert.num.FromU32U8.from height)
  let indices ←
    core.array.from_fn 3#usize
      (direct_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      N) (first1, active1, a, j, fors_indices)
  let sibs ←
    nodes sk seed fors_addr indices
      active1 j
  let a1 := Array.repeat N 0#u8
  let writes := Array.repeat 3#usize (0#usize, a1)
  direct_ticket_loop
    { start := 0#usize, «end» := active1 } fors_stride first1 j sibs writes

def
  split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : split_ticket.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (split_ticket.closure N))
  := do
  let (i, i1, i2, i3, v, i4, i5) := c
  let i6 ← i1 - 1#usize
  let i7 ← lift (core.cmp.impls.OrdUsize.min tupled_args i6)
  let t ← i + i7
  let i8 ← lift (UScalar.cast .U32 t)
  let i9 ← i2 - i3
  let i10 ← i8 <<< i9
  let i11 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) v t
  let i12 ← i11 >>> i3
  let i13 ← lift (i12 ^^^ 1#u32)
  let root_idx ← i10 + i13
  let i14 ← root_idx <<< i4
  let i15 ← i14 + i5
  ok (i15, c)

def
  split_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : split_ticket.closure N)
  (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def
  split_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnOnce
  (split_ticket.closure N) Std.Usize Std.U32 := {
  call_once :=
    split_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def
  split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnMut
  (split_ticket.closure N) Std.Usize Std.U32 := {
  FnOnceInst :=
    split_ticket.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    N
  call_mut :=
    split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

@[rust_loop_body]
def split_ticket_loop.body
  {N : Std.Usize} (chunk : Std.U32) (split_base : Std.Usize)
  (chunks : Std.Usize) (vals : Array (Array Std.U8 N) 3#usize)
  (iter : core.ops.range.Range Std.Usize)
  (writes : Array (Std.Usize × (Array Std.U8 N)) 3#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Std.Usize ×
    (Array Std.U8 N)) 3#usize)) (Array (Std.Usize × (Array Std.U8 N))
    3#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done writes)
  | some lane =>
    let i ← lane * chunks
    let i1 ← split_base + i
    let i2 ← lift (UScalar.cast .Usize chunk)
    let i3 ← i1 + i2
    let a ← Array.index_usize vals lane
    let a1 ← Array.update writes lane (i3, a)
    ok (cont (iter1, a1))

@[rust_loop]
def split_ticket_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (chunk : Std.U32)
  (split_base : Std.Usize) (chunks : Std.Usize)
  (vals : Array (Array Std.U8 N) 3#usize)
  (writes : Array (Std.Usize × (Array Std.U8 N)) 3#usize) :
  Result (Array (Std.Usize × (Array Std.U8 N)) 3#usize)
  := do
  loop
    (fun (iter1, writes1) => split_ticket_loop.body chunk
      split_base chunks vals iter1 writes1)
    (iter, writes)

def split_ticket
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (fors_indices : alloc.vec.Vec Std.U32)
  (a : Std.U32) (first : Std.U16) (active : Std.U8) (height : Std.U8)
  (sub_h : Std.U8) (chunk : Std.U32) (split_base : Std.Usize)
  (chunks : Std.Usize) :
  Result (Array (Std.Usize × (Array Std.U8 N)) 3#usize)
  := do
  let first1 ← lift (UScalar.cast .Usize first)
  let active1 ← lift (UScalar.cast .Usize active)
  let j ← lift (core.convert.num.FromU32U8.from height)
  let sub ← lift (core.convert.num.FromU32U8.from sub_h)
  let split ← j - sub
  let indices ←
    core.array.from_fn 3#usize
      (split_ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      N) (first1, active1, a, j, fors_indices, split, chunk)
  let vals ←
    nodes sk seed fors_addr indices
      active1 sub
  let a1 := Array.repeat N 0#u8
  let writes := Array.repeat 3#usize (0#usize, a1)
  split_ticket_loop { start := 0#usize, «end» := active1 }
    chunk split_base chunks vals writes
end
end slhdsa.ParallelForsTicket
