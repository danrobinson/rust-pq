import Parallel.ScalarForsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelScalarFors
variable [host : Host]

@[rust_loop_body]
def low_ticket_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (t : Std.U32) (a : Std.U32) (idx : Std.U32)
  (base : Std.Usize) (iter : core.ops.range.Range Std.U32)
  (journal : Array (Std.Usize × (Array Std.U8 N)) 14#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Std.Usize ×
    (Array Std.U8 N)) 14#usize)) (Array (Std.Usize × (Array Std.U8 N))
    14#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done journal)
  | some j =>
    let i ← idx >>> j
    let s ← lift (i ^^^ 1#u32)
    let i1 ← a - j
    let i2 ← t <<< i1
    let i3 ← i2 + s
    let node ← node sk i3 j seed fors_addr
    let i4 ← base + 1#usize
    let i5 ← lift (UScalar.cast .Usize j)
    let i6 ← i4 + i5
    let i7 ← lift (UScalar.cast .Usize j)
    let a1 ← Array.update journal i7 (i6, node)
    ok (cont (iter1, a1))

@[rust_loop]
def low_ticket_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (fors_addr : address.Adrs) (t : Std.U32)
  (a : Std.U32) (journal : Array (Std.Usize × (Array Std.U8 N)) 14#usize)
  (idx : Std.U32) (base : Std.Usize) :
  Result (Array (Std.Usize × (Array Std.U8 N)) 14#usize)
  := do
  loop
    (fun (iter1, journal1) => low_ticket_loop.body sk
      seed fors_addr t a idx base iter1 journal1)
    (iter, journal)

def low_ticket
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (fors_indices : alloc.vec.Vec Std.U32)
  (t : Std.U32) (a : Std.U32) (low_h : Std.U32) (fors_stride : Std.Usize)
  (journal : Array (Std.Usize × (Array Std.U8 N)) 14#usize) :
  Result ((Std.Usize × (Array Std.U8 N)) × (Array (Std.Usize × (Array Std.U8
    N)) 14#usize))
  := do
  let i ← lift (UScalar.cast .Usize t)
  let idx ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
      fors_indices i
  let i1 ← lift (UScalar.cast .Usize t)
  let base ← i1 * fors_stride
  let i2 ← t <<< a
  let i3 ← i2 + idx
  let secret ← shake.fors.fors_sk_gen sk seed fors_addr i3
  let journal1 ←
    low_ticket_loop
      { start := 0#u32, «end» := low_h } sk seed fors_addr t a journal idx
      base
  ok ((base, secret), journal1)
end slhdsa.ParallelScalarFors
