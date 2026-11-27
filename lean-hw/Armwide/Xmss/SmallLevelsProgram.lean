import Armwide.Xmss.SmallParents
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ArmXmss

def smallSliceAt (cap : Usize) (state : Array U32 8#usize) (a : address.Adrs) (first : U32)
    (s : Slice (Array U8 16#usize)) (count : Usize) : Result (Slice (Array U8 16#usize)) :=
  if h : s.val.length=cap.val then
    ok (Array.to_slice (smallBuffer (cap:=cap) state a first (Array.from s.val h) count))
  else fail .panic

abbrev smallSlice := smallSliceAt 16#usize

/-- Native Arm XMSS reduction for 16-byte nodes. -/
@[rust_loop_body]
def xmss.arm.batch_root_16_loop0.body
  (state : Array Std.U32 8#usize) (adrs : address.Adrs) (first : Std.U32)
  (count : Std.Usize) (iter : core.ops.range.RangeInclusive Std.U32)
  (roots : Array (Array Std.U8 16#usize) 16#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.U32) × (Array (Array
    Std.U8 16#usize) 16#usize)) (Array (Array Std.U8 16#usize) 16#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepU32 iter
  match o with
  | none => ok (done roots)
  | some level =>
    let a ← address.Adrs.with_type adrs address.TREE
    let adr ← address.Adrs.with_word2 a level
    let i ← first >>> level
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut roots)
    let i1 ← count >>> level
    let s1 ← smallSlice state adr i s i1
    let roots1 := to_slice_mut_back s1
    ok (cont (iter1, roots1))

/-- Native Arm XMSS reduction for 16-byte nodes. -/
@[rust_loop]
def xmss.arm.batch_root_16_loop0
  (iter : core.ops.range.RangeInclusive Std.U32)
  (state : Array Std.U32 8#usize) (adrs : address.Adrs) (first : Std.U32)
  (count : Std.Usize) (roots : Array (Array Std.U8 16#usize) 16#usize) :
  Result (Array (Array Std.U8 16#usize) 16#usize)
  := do
  loop
    (fun (iter1, roots1) => xmss.arm.batch_root_16_loop0.body state adrs first
      count iter1 roots1)
    (iter, roots)

end slhdsa.ArmXmss
