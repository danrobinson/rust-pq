import Armwide.Xmss.PhysicalParents
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ArmXmss

def parentSliceAt (cap : Usize) {N : Usize} (enabled : Bool) (state : Array U64 8#usize) (a : address.Adrs)
    (first : U32) (s : Slice (Array U8 N)) (count : Usize) : Result (Usize × Slice (Array U8 N)) :=
  if h : s.val.length = cap.val then
    let packed := pairedBuffer (cap:=cap) state a first (Array.from s.val h) count enabled
    ok (packed.1,Array.to_slice packed.2)
  else fail .panic

abbrev parentSlice {N} := @parentSliceAt 16#usize N

/-- Extracted native XMSS level traversal. -/
@[rust_loop_body]
def xmss.arm.batch_root_512_loop0.body
  (enabled : Bool) {N : Std.Usize} (a : Array Std.U8 N) (a1 : Array Std.U32 8#usize)
  (a2 : Array Std.U64 8#usize) (adrs : address.Adrs) (first : Std.U32)
  (count : Std.Usize) (iter : core.ops.range.RangeInclusive Std.U32)
  (roots : Array (Array Std.U8 N) 16#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.U32) × (Array (Array
    Std.U8 N) 16#usize)) (Array (Array Std.U8 N) 16#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepU32 iter
  match o with
  | none => ok (done roots)
  | some level =>
    let a3 ← address.Adrs.with_type adrs address.TREE
    let adr ← address.Adrs.with_word2 a3 level
    let level_first ← first >>> level
    let level_count ← count >>> level
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut roots)
    let (done1, s1) ←
      parentSlice enabled a2 adr level_first s level_count
    let roots1 := to_slice_mut_back s1
    let roots2 ←
      xmss.arm.batch_root_512_loop0_loop0
        { start := done1, «end» := level_count } a a1 a2 roots1 adr
        level_first
    ok (cont (iter1, roots2))

/-- Extracted native XMSS level traversal. -/
@[rust_loop]
def xmss.arm.batch_root_512_loop0
  (enabled : Bool) {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.U32)
  (a : Array Std.U8 N) (a1 : Array Std.U32 8#usize)
  (a2 : Array Std.U64 8#usize) (adrs : address.Adrs) (first : Std.U32)
  (count : Std.Usize) (roots : Array (Array Std.U8 N) 16#usize) :
  Result (Array (Array Std.U8 N) 16#usize)
  := do
  loop
    (fun (iter1, roots1) => xmss.arm.batch_root_512_loop0.body enabled a a1 a2 adrs
      first count iter1 roots1)
    (iter, roots)
end slhdsa.ArmXmss
