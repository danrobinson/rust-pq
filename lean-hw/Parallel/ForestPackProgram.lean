import Parallel.SignJoinProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForestPack
@[rust_loop_body]
def pack_fors_loop.body
  {N : Std.Usize}
  (iter : core.slice.iter.Iter (Option (Array Std.U8 N)))
  (sig_fors : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.slice.iter.Iter (Option
    (Array Std.U8 N))) × (alloc.vec.Vec Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done sig_fors)
  | some slot =>
    let o1 ← ParallelSignJoin.readCell slot
    let a ← core.option.Option.expect o1 (toStr "all FORS slots filled")
    let s ← lift (Array.to_slice a)
    let sig_fors1 ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig_fors s
    ok (cont (iter1, sig_fors1))

@[rust_loop]
def pack_fors_loop
  {N : Std.Usize}
  (iter : core.slice.iter.Iter (Option (Array Std.U8 N)))
  (sig_fors : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig_fors1) => pack_fors_loop.body iter1
      sig_fors1)
    (iter, sig_fors)

def pack_fors
  {N : Std.Usize} (p : params.Params)
  (fors_direct : alloc.vec.Vec (Option (Array Std.U8 N)))
  :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← params.Params.fors_sig_bytes p
  let sig_fors := alloc.vec.Vec.with_capacity Std.U8 i
  let iter ←
    core.slice.Slice.iter fors_direct.deref
  pack_fors_loop iter sig_fors
end slhdsa.ParallelForestPack
