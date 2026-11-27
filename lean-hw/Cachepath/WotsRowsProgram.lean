import Cachepath.Subtree
import Cachepath.WotsCallbacks
import Shakebatch.Pair
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.cache.builder.nativeShake.Vector
open ShakeBatch
set_option linter.concreteInstances false
set_option linter.unusedVariables false
variable [machine : Machine]

class Leaves (machine : Machine) where
  gen {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Array U32 machine.width →
    Result (Array (Array U8 N) machine.width)

variable [Leaves machine]
noncomputable section

@[reducible]
def fill_xmss_leaves.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize × Std.Usize

@[reducible]
def hash_pairs.closure_3 (N : Std.Usize) :=
  Slice (Array Std.U8 N)

@[reducible]
def hash_pairs.closure_2 (N : Std.Usize) :=
  Slice (Array Std.U8 N)

@[reducible]
def hash_pairs.closure_1 (N : Std.Usize) :=
  address.Adrs × Std.U32 × Std.Usize

@[reducible]
def hash_pairs.closure (N : Std.Usize) :=
  Std.Usize × Std.Usize

def
  fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  {N : Std.Usize} (c : fill_xmss_leaves.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.U32 × (fill_xmss_leaves.closure N))
  := do
  let (i, i1, i2) := c
  let i3 ← i + i1
  let i4 ← i2 - 1#usize
  let i5 ← lift (core.cmp.impls.OrdUsize.min tupled_args i4)
  let i6 ← i3 + i5
  let i7 ← lift (UScalar.cast .U32 i6)
  ok (i7, c)

def
  fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
  {N : Std.Usize} (c : fill_xmss_leaves.closure N)
  (i : Std.Usize) :
  Result Std.U32
  := do
  let (i1, _) ←
    fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      c i
  ok i1

@[reducible]
def
  fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnOnce
  (fill_xmss_leaves.closure N) Std.Usize Std.U32 := {
  call_once :=
    fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once
}

@[reducible]
def
  fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  (N : Std.Usize) : core.ops.function.FnMut
  (fill_xmss_leaves.closure N) Std.Usize Std.U32 := {
  FnOnceInst :=
    fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU32
    N
  call_mut :=
    fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
}

@[rust_loop_body]
def fill_xmss_leaves_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (start : Std.Usize) (len : Std.Usize)
  (out : Slice (Array Std.U8 N)) (off : Std.Usize) :
  Result (ControlFlow ((Slice (Array Std.U8 N)) × Std.Usize) (Slice (Array
    Std.U8 N)))
  := do
  if off < len
  then
    let i ← len - off
    let active ← lift (core.cmp.impls.OrdUsize.min i machine.width)
    let keys ←
      core.array.from_fn machine.width
        (fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        N) (start, off, active)
    let batch ← Leaves.gen sk seed addr keys
    let i1 ← off + active
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N)) out
        { start := off, «end» := i1 }
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) batch
        { «end» := active }
    let s2 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
        core.marker.CopyU8) s s1
    let out1 := index_mut_back s2
    ok (cont (out1, i1))
  else ok (done out)

@[rust_loop]
def fill_xmss_leaves_loop
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (start : Std.Usize) (out : Slice (Array Std.U8 N))
  (len : Std.Usize) (off : Std.Usize) :
  Result (Slice (Array Std.U8 N))
  := do
  loop
    (fun (out1, off1) => fill_xmss_leaves_loop.body sk
      seed addr start len out1 off1)
    (out, off)

def fill_xmss_leaves
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (start : Std.Usize) (out : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  let len := Slice.len out
  fill_xmss_leaves_loop sk seed addr start out len 0#usize

def
  hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : hash_pairs.closure_3 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (hash_pairs.closure_3 N))
  := do
  let i ← 2#usize * tupled_args
  let i1 ← i + 1#usize
  let a ← Slice.index_usize c i1
  ok (a, c)

def
  hash_pairs.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : hash_pairs.closure_3 N)
  (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def
  hash_pairs.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (hash_pairs.closure_3 N) Std.Usize (Array Std.U8 N) := {
  call_once :=
    hash_pairs.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def
  hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut
  (hash_pairs.closure_3 N) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    hash_pairs.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  {N : Std.Usize} (c : hash_pairs.closure_2 N)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U8 N) × (hash_pairs.closure_2 N))
  := do
  let i ← 2#usize * tupled_args
  let a ← Slice.index_usize c i
  ok (a, c)

def
  hash_pairs.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
  {N : Std.Usize} (c : hash_pairs.closure_2 N)
  (i : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let (a, _) ←
    hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
      c i
  ok a

@[reducible]
def
  hash_pairs.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnOnce
  (hash_pairs.closure_2 N) Std.Usize (Array Std.U8 N) := {
  call_once :=
    hash_pairs.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N.call_once
}

@[reducible]
def
  hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
  (N : Std.Usize) : core.ops.function.FnMut
  (hash_pairs.closure_2 N) Std.Usize (Array Std.U8 N) := {
  FnOnceInst :=
    hash_pairs.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU8N
    N
  call_mut :=
    hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
}

def
  hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
  {N : Std.Usize} (c : hash_pairs.closure_1 N)
  (tupled_args : Std.Usize) :
  Result (address.Adrs × (hash_pairs.closure_1 N))
  := do
  let (a, i, i1) := c
  let a1 ← address.Adrs.with_type a address.TREE
  let a2 ← address.Adrs.with_word2 a1 i
  let i2 ← i1 + tupled_args
  let i3 ← lift (UScalar.cast .U32 i2)
  let a3 ← address.Adrs.with_word3 a2 i3
  ok (a3, c)

def
  hash_pairs.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
  {N : Std.Usize} (c : hash_pairs.closure_1 N)
  (i : Std.Usize) :
  Result address.Adrs
  := do
  let (a, _) ←
    hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
      c i
  ok a

@[reducible]
def
  hash_pairs.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs
  (N : Std.Usize) : core.ops.function.FnOnce
  (hash_pairs.closure_1 N) Std.Usize address.Adrs := {
  call_once :=
    hash_pairs.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs.call_once
}

@[reducible]
def
  hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs
  (N : Std.Usize) : core.ops.function.FnMut
  (hash_pairs.closure_1 N) Std.Usize address.Adrs := {
  FnOnceInst :=
    hash_pairs.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeAdrs
    N
  call_mut :=
    hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
}

def
  hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  {N : Std.Usize} (c : hash_pairs.closure N)
  (tupled_args : Std.Usize) :
  Result (Std.Usize × (hash_pairs.closure N))
  := do
  let (i, i1) := c
  let i2 ← i1 - 1#usize
  let i3 ← lift (core.cmp.impls.OrdUsize.min tupled_args i2)
  let i4 ← i + i3
  ok (i4, c)

def
  hash_pairs.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
  {N : Std.Usize} (c : hash_pairs.closure N)
  (i : Std.Usize) :
  Result Std.Usize
  := do
  let (i1, _) ←
    hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
      c i
  ok i1

@[reducible]
def
  hash_pairs.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
  (N : Std.Usize) : core.ops.function.FnOnce
  (hash_pairs.closure N) Std.Usize Std.Usize := {
  call_once :=
    hash_pairs.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
}

@[reducible]
def
  hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize
  (N : Std.Usize) : core.ops.function.FnMut
  (hash_pairs.closure N) Std.Usize Std.Usize := {
  FnOnceInst :=
    hash_pairs.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
    N
  call_mut :=
    hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
}

@[rust_loop_body]
def hash_pairs_loop.body
  {N : Std.Usize} (seed : Array Std.U8 N) (addr : address.Adrs)
  (height : Std.U32) (base_index : Std.Usize)
  (children : Slice (Array Std.U8 N)) (count : Std.Usize)
  (parents : Slice (Array Std.U8 N)) (off : Std.Usize) :
  Result (ControlFlow ((Slice (Array Std.U8 N)) × Std.Usize) (Slice (Array
    Std.U8 N)))
  := do
  if off < count
  then
    let i ← count - off
    let active ← lift (core.cmp.impls.OrdUsize.min i machine.width)
    let ids ←
      core.array.from_fn machine.width
        (hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize
        N) (off, active)
    let addresses ←
      core.array.Array.map
        (hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs
        N) ids (addr, height, base_index)
    let left ←
      core.array.Array.map
        (hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) ids children
    let right ←
      core.array.Array.map
        (hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N
        N) ids children
    let batch ← ShakeBatch.shake.batch.pair seed addresses left right
    let i1 ← off + active
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 N)) parents
        { start := off, «end» := i1 }
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) batch
        { «end» := active }
    let s2 ←
      core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N
        core.marker.CopyU8) s s1
    let parents1 := index_mut_back s2
    ok (cont (parents1, i1))
  else ok (done parents)

@[rust_loop]
def hash_pairs_loop
  {N : Std.Usize} (seed : Array Std.U8 N) (addr : address.Adrs)
  (height : Std.U32) (base_index : Std.Usize)
  (children : Slice (Array Std.U8 N)) (parents : Slice (Array Std.U8 N))
  (count : Std.Usize) (off : Std.Usize) :
  Result (Slice (Array Std.U8 N))
  := do
  loop
    (fun (parents1, off1) => hash_pairs_loop.body seed
      addr height base_index children count parents1 off1)
    (parents, off)

def hash_pairs
  {N : Std.Usize} (seed : Array Std.U8 N) (addr : address.Adrs)
  (height : Std.U32) (base_index : Std.Usize)
  (children : Slice (Array Std.U8 N)) (parents : Slice (Array Std.U8 N)) :
  Result (Slice (Array Std.U8 N))
  := do
  let count := Slice.len parents
  hash_pairs_loop seed addr height base_index children
    parents count 0#usize

@[instance_reducible] def backend (available : Usize → Result Bool) : Backend where
  available := available
  fill := fill_xmss_leaves
  pairs := hash_pairs

@[instance_reducible] def single [stream : Stream] : Subtree.Single where
  leaf := ShakeBatch.shake.batch.keygen

end
end slhdsa.cache.builder.nativeShake.Vector
