-- Extracted from the production per-batch writes in cache::shake_ops::simd.
module
public import Aeneas
public import Cacheops.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace CacheopsRust

@[rust_loop_body]
def cell_sig_loop.body
  {N : Std.Usize} {WIDTH : Std.Usize} (values : Array (Array Std.U8 N) WIDTH)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.Usize)) × (alloc.vec.Vec Std.U8)) (alloc.vec.Vec
    Std.U8))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) iter
  match o with
  | none => ok (done sig)
  | some p =>
    let (lane, id) := p
    let i ← id * N
    let i1 ← id + 1#usize
    let i2 ← i1 * N
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i, «end» := i2 }
    let a ← Array.index_usize values lane
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sig1 := index_mut_back s2
    ok (cont (iter1, sig1))

@[rust_loop]
def cell_sig_loop
  {N : Std.Usize} {WIDTH : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (values : Array (Array Std.U8 N) WIDTH)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => cell_sig_loop.body values iter1 sig1)
    (iter, sig)

def cell_sig
  {N : Std.Usize} {WIDTH : Std.Usize} (batch : Slice Std.Usize)
  (values : Array (Array Std.U8 N) WIDTH) (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← core.slice.Slice.iter batch
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) i
  cell_sig_loop iter values sig

@[rust_loop_body]
def cell_key_loop.body
  {N : Std.Usize} {WIDTH : Std.Usize} (values : Array (Array Std.U8 N) WIDTH)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (endpoints : Array (Array Std.U8 N) 67#usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.Usize)) × (Array (Array Std.U8 N) 67#usize))
    (Array (Array Std.U8 N) 67#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) iter
  match o with
  | none => ok (done endpoints)
  | some p =>
    let (lane, id) := p
    let a ← Array.index_usize values lane
    let a1 ← Array.update endpoints id a
    ok (cont (iter1, a1))

@[rust_loop]
def cell_key_loop
  {N : Std.Usize} {WIDTH : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.Usize)) (values : Array (Array Std.U8 N) WIDTH)
  (endpoints : Array (Array Std.U8 N) 67#usize) :
  Result (Array (Array Std.U8 N) 67#usize)
  := do
  loop
    (fun (iter1, endpoints1) => cell_key_loop.body values iter1 endpoints1)
    (iter, endpoints)

def cell_key
  {N : Std.Usize} {WIDTH : Std.Usize} (batch : Slice Std.Usize)
  (values : Array (Array Std.U8 N) WIDTH)
  (endpoints : Array (Array Std.U8 N) 67#usize) :
  Result (Array (Array Std.U8 N) 67#usize)
  := do
  let i ← core.slice.Slice.iter batch
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.Usize) i
  cell_key_loop iter values endpoints

end CacheopsRust
