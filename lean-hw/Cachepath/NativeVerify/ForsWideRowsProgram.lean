import Cachepath.NativeVerify.ForsFused
import Fused.Program
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsWideRows
open ShakeBatch
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance rowsProgramMachine : Machine := Fused.machine kernel

@[rust_loop_body]
def leaves_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Slice Std.U32)
  (out : Slice (Array Std.U8 N)) (i : Std.Usize) :
  Result (ControlFlow ((Slice (Array Std.U8 N)) × Std.Usize) (Slice (Array
    Std.U8 N)))
  := do
  let i1 := Slice.len indices
  if i < i1
  then
    let i2 := Slice.len indices
    let i3 ← i2 - i
    let i4 ← (ok 8#usize : Result Usize)
    let active ← lift (core.cmp.impls.OrdUsize.min i3 i4)
    let batch := Array.repeat 8#usize 0#u32
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) batch
        { «end» := active }
    let i5 ← i + active
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U32) indices { start := i, «end» := i5 }
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU32 s s1
    let batch1 := index_mut_back s2
    let leaves ←
      (ForsFused.fused kernel.active) sk seed addr batch1 active
    let (s3, index_mut_back1) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N)) out
        { start := i, «end» := i5 }
    let s4 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) leaves
        { «end» := active }
    let s5 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
        core.marker.CopyU8) s3 s4
    let out1 := index_mut_back1 s5
    ok (cont (out1, i5))
  else ok (done out)

@[rust_loop]
def leaves_loop
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Slice Std.U32)
  (out : Slice (Array Std.U8 N)) (i : Std.Usize) :
  Result (Slice (Array Std.U8 N))
  := do
  loop
    (fun (out1, i1) => leaves_loop.body sk seed
      addr indices out1 i1)
    (out, i)

@[reducible]
def leaves
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Slice Std.U32)
  (out : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  leaves_loop sk seed addr indices out 0#usize

@[rust_loop_body]
def pairs_loop0_loop0.body
  {N : Std.Usize} (tree_adrs : address.Adrs) (level : Std.U32)
  (node_indices : Slice Std.U32) (children : Slice (Array Std.U8 N))
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array address.Adrs
    8#usize) × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N)
    8#usize)) ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize)
    × (Array (Array Std.U8 N) 8#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (addrs, left, right))
  | some lane =>
    let a ← address.Adrs.with_word2 tree_adrs level
    let i1 ← i + lane
    let i2 ← Slice.index_usize node_indices i1
    let a1 ← address.Adrs.with_word3 a i2
    let a2 ← Array.update addrs lane a1
    let i3 ← 2#usize * i1
    let a3 ← Slice.index_usize children i3
    let a4 ← Array.update left lane a3
    let i4 ← 2#usize * i1
    let i5 ← i4 + 1#usize
    let a5 ← Slice.index_usize children i5
    let a6 ← Array.update right lane a5
    ok (cont (iter1, a2, a4, a6))

@[rust_loop]
def pairs_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (tree_adrs : address.Adrs) (level : Std.U32) (node_indices : Slice Std.U32)
  (children : Slice (Array Std.U8 N)) (addrs : Array address.Adrs 8#usize)
  (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) (i : Std.Usize) :
  Result ((Array address.Adrs 8#usize) × (Array (Array Std.U8 N) 8#usize) ×
    (Array (Array Std.U8 N) 8#usize))
  := do
  loop
    (fun (iter1, addrs1, left1, right1) =>
      pairs_loop0_loop0.body tree_adrs level
      node_indices children i iter1 addrs1 left1 right1)
    (iter, addrs, left, right)

@[rust_loop_body]
def pairs_loop0.body
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (level : Std.U32) (node_indices : Slice Std.U32)
  (children : Slice (Array Std.U8 N)) (out : Slice (Array Std.U8 N))
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) (i : Std.Usize) :
  Result (ControlFlow ((Slice (Array Std.U8 N)) × (Array address.Adrs 8#usize)
    × (Array (Array Std.U8 N) 8#usize) × (Array (Array Std.U8 N) 8#usize) ×
    Std.Usize) (Slice (Array Std.U8 N)))
  := do
  let i1 := Slice.len node_indices
  if i < i1
  then
    let i2 := Slice.len node_indices
    let i3 ← i2 - i
    let i4 ← (ok 8#usize : Result Usize)
    let active ← lift (core.cmp.impls.OrdUsize.min i3 i4)
    let (addrs1, left1, right1) ←
      pairs_loop0_loop0
        { start := 0#usize, «end» := active } tree_adrs level node_indices
        children addrs left right i
    let parents ← (ActiveHash.pair_active kernel.active) seed addrs1 left1 right1 active
    let i5 ← i + active
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N)) out
        { start := i, «end» := i5 }
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
        parents { «end» := active }
    let s2 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
        core.marker.CopyU8) s s1
    let out1 := index_mut_back s2
    ok (cont (out1, addrs1, left1, right1, i5))
  else ok (done out)

@[rust_loop]
def pairs_loop0
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (level : Std.U32) (node_indices : Slice Std.U32)
  (children : Slice (Array Std.U8 N)) (out : Slice (Array Std.U8 N))
  (addrs : Array address.Adrs 8#usize) (left : Array (Array Std.U8 N) 8#usize)
  (right : Array (Array Std.U8 N) 8#usize) (i : Std.Usize) :
  Result (Slice (Array Std.U8 N))
  := do
  loop
    (fun (out1, addrs1, left1, right1, i1) =>
      pairs_loop0.body seed tree_adrs level
      node_indices children out1 addrs1 left1 right1 i1)
    (out, addrs, left, right, i)

def pairs
  {N : Std.Usize} (seed : Array Std.U8 N) (tree_adrs : address.Adrs)
  (level : Std.U32) (node_indices : Slice Std.U32)
  (children : Slice (Array Std.U8 N)) (out : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  let addrs := Array.repeat 8#usize tree_adrs
  let a := Array.repeat N 0#u8
  let left := Array.repeat 8#usize a
  let a1 := Array.repeat N 0#u8
  let right := Array.repeat 8#usize a1
  pairs_loop0 seed tree_adrs level node_indices
    children out addrs left right 0#usize
end slhdsa.NativeVerify.ForsWideRows
