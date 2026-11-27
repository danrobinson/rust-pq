import Kappleouter.Top
import Armplatform.Internal
open Aeneas Aeneas.Std Result
namespace MetalHostHash
noncomputable section


def shake_prf_msg
  {N : Std.Usize} (sk_prf : Array Std.U8 N) (opt_rand : Array Std.U8 N)
  (msg : Slice Std.U8) :
  Result (Array Std.U8 N)
  := do
  let i ← 2#usize * N
  let i1 := Slice.len msg
  let i2 ← i + i1
  let input := alloc.vec.Vec.with_capacity Std.U8 i2
  let s ← lift (Array.to_slice sk_prf)
  let input1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input s
  let s1 ← lift (Array.to_slice opt_rand)
  let input2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input1 s1
  let input3 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input2 msg
  let out := Array.repeat N 0#u8
  let s2 := alloc.vec.Vec.deref input3
  let (s3, to_slice_mut_back) ← lift (Array.to_slice_mut out)
  let s4 ← KappleouterRust.shake256.shake256 s2 s3
  ok (to_slice_mut_back s4)


def shake_h_msg
  {N : Std.Usize} (p : slhdsa.params.Params) (r : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (pk_root : Array Std.U8 N) (msg : Slice Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← 3#usize * N
  let i1 := Slice.len msg
  let i2 ← i + i1
  let input := alloc.vec.Vec.with_capacity Std.U8 i2
  let s ← lift (Array.to_slice r)
  let input1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input s
  let s1 ← lift (Array.to_slice pk_seed)
  let input2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input1 s1
  let s2 ← lift (Array.to_slice pk_root)
  let input3 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input2 s2
  let input4 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 input3 msg
  let out ← alloc.vec.from_elem core.clone.CloneU8 0#u8 p.m
  let s3 := alloc.vec.Vec.deref input4
  let (s4, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut out)
  let s5 ← KappleouterRust.shake256.shake256 s3 s4
  ok (deref_mut_back s5)


def with_context
  (m : Slice Std.U8) (ctx : Slice Std.U8) : Result (alloc.vec.Vec Std.U8) := do
  let i := Slice.len ctx
  let i1 ← 2#usize + i
  let i2 := Slice.len m
  let i3 ← i1 + i2
  let mp := alloc.vec.Vec.with_capacity Std.U8 i3
  let mp1 ← alloc.vec.Vec.push mp 0#u8
  let i4 := Slice.len ctx
  let i5 ← lift (UScalar.cast .U8 i4)
  let mp2 ← alloc.vec.Vec.push mp1 i5
  let mp3 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 mp2 ctx
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 mp3 m


def digest_tree
  (p : slhdsa.params.Params) (digest : Slice Std.U8) : Result Std.U64 := do
  let lo ← slhdsa.params.Params.md_bytes p
  let i ← slhdsa.params.Params.tree_bytes p
  let i1 ← lo + i
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := lo, «end» := i1 }
  let i2 ← slhdsa.util.to_int s
  let i3 ← slhdsa.params.Params.tree_bits p
  let i4 ← 64#u32 - i3
  let i5 ← core.num.U64.MAX >>> i4
  ok (i2 &&& i5)


def digest_leaf
  (p : slhdsa.params.Params) (digest : Slice Std.U8) : Result Std.U32 := do
  let i ← slhdsa.params.Params.md_bytes p
  let i1 ← slhdsa.params.Params.tree_bytes p
  let lo ← i + i1
  let i2 ← slhdsa.params.Params.leaf_bytes p
  let i3 ← lo + i2
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := lo, «end» := i3 }
  let i4 ← slhdsa.util.to_int s
  let i5 ← 1#u64 <<< p.hp
  let i6 ← i5 - 1#u64
  let i7 ← lift (i4 &&& i6)
  ok (UScalar.cast .U32 i7)

end
end MetalHostHash
