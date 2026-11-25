import Parallel.UncachedCaller
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ParallelSignJoin
abbrev Cells (N : Usize) := Option (alloc.vec.Vec U8) × Option (alloc.vec.Vec (Array U8 N)) ×
  alloc.vec.Vec (Option (alloc.vec.Vec U8))
abbrev Join := {N : Usize} → params.Params → Slice U8 → Array U8 N → Array U8 N →
  address.Adrs → Array U8 N → U64 → U32 → Usize → Result (Cells N)
/-- Read-only view after the pool join. Unpublished slots still produce none. -/
def readCell {α : Type} (v : Option α) : Result (Option α) := ok v
variable (threadsAvailable : Result Usize) (join : Join)
@[rust_loop_body]
def run_loop0_loop0.body
  {N : Std.Usize} (hp : Std.Usize) (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (signature : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done signature)
  | some h =>
    let i ← j * hp
    let i1 ← i + h
    let a ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
        N)) xmss_auth i1
    let s ← lift (Array.to_slice a)
    let signature1 ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 signature s
    ok (cont (iter1, signature1))

@[rust_loop]
def run_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (hp : Std.Usize)
  (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (signature : alloc.vec.Vec Std.U8) (j : Std.Usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, signature1) =>
      run_loop0_loop0.body hp xmss_auth j
      iter1 signature1)
    (iter, signature)

@[rust_loop_body]
def run_loop0.body
  {N : Std.Usize} (hp : Std.Usize)
  (wots_sigs : alloc.vec.Vec (Option (alloc.vec.Vec
  Std.U8))) (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (iter : core.ops.range.Range Std.Usize) (signature : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done signature)
  | some j =>
    let ol ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (Option (alloc.vec.Vec Std.U8))) wots_sigs j
    let o1 ← readCell ol
    let v ← core.option.Option.expect o1 (toStr "all WOTS sigs filled")
    let s := alloc.vec.Vec.deref v
    let signature1 ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 signature s
    let signature2 ←
      run_loop0_loop0
        { start := 0#usize, «end» := hp } hp xmss_auth signature1 j
    ok (cont (iter1, signature2))

@[rust_loop]
def run_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (hp : Std.Usize)
  (wots_sigs : alloc.vec.Vec (Option (alloc.vec.Vec
  Std.U8))) (xmss_auth : alloc.vec.Vec (Array Std.U8 N))
  (signature : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, signature1) => run_loop0.body
      hp wots_sigs xmss_auth iter1 signature1)
    (iter, signature)

def run
  {N : Std.Usize} (p : params.Params) (md : Slice Std.U8) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (fors_addr : address.Adrs) (r : Array Std.U8 N)
  (tree : Std.U64) (leaf : Std.U32) :
  Result (Option (alloc.vec.Vec Std.U8))
  := do
  let threads ← threadsAvailable
  if threads < 2#usize
  then ok none
  else
    if p.hp = 0#u32
    then ok none
    else
      let d ← lift (UScalar.cast .Usize p.d)
      let hp ← lift (UScalar.cast .Usize p.hp)
      let (sig_fors_cell, xmss_auth_cell, wots_sigs) ←
        join p md sk seed fors_addr r tree leaf
          threads
      let o ← readCell sig_fors_cell
      let sig_fors ← core.option.Option.expect o (toStr "FORS sig assembled")
      let o1 ← readCell xmss_auth_cell
      let xmss_auth ←
        core.option.Option.expect o1 (toStr "XMSS auth assembled")
      let i ← params.Params.sig_bytes p
      let signature := alloc.vec.Vec.with_capacity Std.U8 i
      let s ← lift (Array.to_slice r)
      let signature1 ←
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 signature s
      let s1 := alloc.vec.Vec.deref sig_fors
      let signature2 ←
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 signature1 s1
      let signature3 ←
        run_loop0
          { start := 0#usize, «end» := d } hp wots_sigs xmss_auth signature2
      ok (some signature3)
end slhdsa.ParallelSignJoin
