import Shakebatch.WidthEightModel
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelScalarFors
class Host where
  width : Usize
  probe : Usize → Result Bool
  horizontal {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)

variable [host : Host]

def node
  {N : Std.Usize} (sk : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if z >= 3#u32
  then
    if host.width = 8#usize
    then
      let b ← host.probe N
      if b
      then host.horizontal sk seed adrs i z
      else
        let a ← address.Adrs.with_word2 adrs z
        let a1 ← address.Adrs.with_word3 a i
        if z = 0#u32
        then
          let a2 ← shake.fors.fors_sk_gen sk seed adrs i
          shake.hash.thash seed a1 a2
        else
          let i1 ← 2#u32 * i
          let i2 ← z - 1#u32
          let left ← node sk i1 i2 seed adrs
          let i3 ← i1 + 1#u32
          let right ← node sk i3 i2 seed adrs
          shake.hash.thash_pair seed a1 left right
    else
      let a ← address.Adrs.with_word2 adrs z
      let a1 ← address.Adrs.with_word3 a i
      if z = 0#u32
      then
        let a2 ← shake.fors.fors_sk_gen sk seed adrs i
        shake.hash.thash seed a1 a2
      else
        let i1 ← 2#u32 * i
        let i2 ← z - 1#u32
        let left ← node sk i1 i2 seed adrs
        let i3 ← i1 + 1#u32
        let right ← node sk i3 i2 seed adrs
        shake.hash.thash_pair seed a1 left right
  else
    let a ← address.Adrs.with_word2 adrs z
    let a1 ← address.Adrs.with_word3 a i
    if z = 0#u32
    then
      let a2 ← shake.fors.fors_sk_gen sk seed adrs i
      shake.hash.thash seed a1 a2
    else
      let i1 ← 2#u32 * i
      let i2 ← z - 1#u32
      let left ← node sk i1 i2 seed adrs
      let i3 ← i1 + 1#u32
      let right ← node sk i3 i2 seed adrs
      shake.hash.thash_pair seed a1 left right
partial_fixpoint

def direct_node_ticket
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (idx : Std.U32) (height : Std.U32)
  (slot : Std.Usize) :
  Result (Std.Usize × (Array Std.U8 N))
  := do
  let node ← node sk idx height seed fors_addr
  ok (slot, node)

def split_node_ticket
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (fors_addr : address.Adrs) (idx : Std.U32) (height : Std.U32)
  (slot : Std.Usize) :
  Result (Std.Usize × (Array Std.U8 N))
  := do
  let node ← node sk idx height seed fors_addr
  ok (slot, node)

def prepare_direct
  (t : Std.U32) (a : Std.U32) (j : Std.U32) (idx : Std.U32) :
  Result (Std.U32 × Std.U32 × Std.Usize)
  := do
  let i ← lift (UScalar.cast .Usize a)
  let fors_stride ← i + 1#usize
  let i1 ← a - j
  let i2 ← t <<< i1
  let i3 ← idx >>> j
  let i4 ← lift (i3 ^^^ 1#u32)
  let root_idx ← i2 + i4
  let i5 ← lift (UScalar.cast .Usize t)
  let i6 ← i5 * fors_stride
  let i7 ← i6 + 1#usize
  let i8 ← lift (UScalar.cast .Usize j)
  let i9 ← i7 + i8
  ok (root_idx, j, i9)

def prepare_split
  (t : Std.U32) (a : Std.U32) (j : Std.U32) (idx : Std.U32)
  (fors_target : Std.U32) (slot_start : Std.Usize) (c : Std.Usize) :
  Result (Std.U32 × Std.U32 × Std.Usize)
  := do
  let i ← lift (UScalar.cast .Usize a)
  let _ ← i + 1#usize
  let i1 ← a - j
  let i2 ← t <<< i1
  let i3 ← idx >>> j
  let i4 ← lift (i3 ^^^ 1#u32)
  let root_idx ← i2 + i4
  let split ← j - fors_target
  let i5 ← root_idx <<< split
  let i6 ← lift (UScalar.cast .U32 c)
  let i7 ← i5 + i6
  let i8 ← slot_start + c
  ok (i7, fors_target, i8)

def prepare_saturating
  (t : Std.U32) (a : Std.U32) (j : Std.U32) (idx : Std.U32)
  (fors_target : Std.U32) (slot_start : Std.Usize) (c : Std.Usize) :
  Result (Std.U32 × Std.U32 × Std.Usize)
  := do
  let i ← lift (UScalar.cast .Usize a)
  let _ ← i + 1#usize
  let i1 ← a - j
  let i2 ← t <<< i1
  let i3 ← idx >>> j
  let i4 ← lift (i3 ^^^ 1#u32)
  let root_idx ← i2 + i4
  let split ← lift (core.num.U32.saturating_sub j fors_target)
  let i5 ← root_idx <<< split
  let i6 ← lift (UScalar.cast .U32 c)
  let i7 ← i5 + i6
  let i8 ← slot_start + c
  ok (i7, fors_target, i8)
end slhdsa.ParallelScalarFors
