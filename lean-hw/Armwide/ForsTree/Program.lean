import Armwide.ForsTree.Leaves
import Armwide.Xmss.SmallLevelsProgram
import Armwide.Xmss.Levels

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ArmForsTree
open ArmXmss

def fillLeaves {N : Usize} (state : Array U32 8#usize) (sk : Array U8 N) (a : address.Adrs)
    (first : U32) (s : Slice (Array U8 N)) : Result (Slice (Array U8 N)) :=
  ok (Slice.from (List.ofFn (fun i : Fin s.length =>
      row N (fusedLeaf N.val (wv state.val) (bytes sk.val) (adrsS a) (first.val+i.val))))
    (by rw [List.length_ofFn];exact s.property))

/-- Extracted native Arm FORS subtree operation. -/
@[rust_loop_body]
def fors.arm.subtree_loop0.body
  (index : Std.U32) (height : Std.U32) (a : Array Std.U32 8#usize)
  (adrs : address.Adrs) (n : Std.Usize)
  (iter : core.ops.range.RangeInclusive Std.U32)
  (nodes : Array (Array Std.U8 16#usize) 128#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.U32) × (Array (Array
    Std.U8 16#usize) 128#usize)) (Array (Array Std.U8 16#usize) 128#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepU32 iter
  match o with
  | none => ok (done nodes)
  | some level =>
    let i ← height - level
    let first ← index <<< i
    let adr ← address.Adrs.with_word2 adrs level
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut nodes)
    let i1 ← n >>> level
    let s1 ← smallSliceAt 128#usize a adr first s i1
    let nodes1 := to_slice_mut_back s1
    ok (cont (iter1, nodes1))

/-- Extracted native Arm FORS subtree operation. -/
@[rust_loop]
def fors.arm.subtree_loop0
  (iter : core.ops.range.RangeInclusive Std.U32) (index : Std.U32)
  (height : Std.U32) (a : Array Std.U32 8#usize) (adrs : address.Adrs)
  (n : Std.Usize) (nodes : Array (Array Std.U8 16#usize) 128#usize) :
  Result (Array (Array Std.U8 16#usize) 128#usize)
  := do
  loop
    (fun (iter1, nodes1) => fors.arm.subtree_loop0.body index height a adrs n
      iter1 nodes1)
    (iter, nodes)

/-- Extracted native Arm FORS subtree operation. -/
@[rust_loop_body]
def fors.arm.subtree_loop1_loop0.body
  {N : Std.Usize} (a : Array Std.U8 N) (a1 : Array Std.U32 8#usize)
  (a2 : Array Std.U64 8#usize) (first : Std.U32) (adr : address.Adrs)
  (iter : core.ops.range.Range Std.Usize)
  (nodes : Array (Array Std.U8 N) 128#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) 128#usize)) (Array (Array Std.U8 N) 128#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done nodes)
  | some j =>
    let i ← lift (UScalar.cast .U32 j)
    let i1 ← first + i
    let a3 ← address.Adrs.with_word3 adr i1
    let i2 ← 2#usize * j
    let a4 ← Array.index_usize nodes i2
    let i3 ← i2 + 1#usize
    let a5 ← Array.index_usize nodes i3
    let a6 ←
      hash.thash_pair { pk_seed := a, state := a1, state512 := a2 } a3 a4 a5
    let a7 ← Array.update nodes j a6
    ok (cont (iter1, a7))

/-- Extracted native Arm FORS subtree operation. -/
@[rust_loop]
def fors.arm.subtree_loop1_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize)
  (nodes : Array (Array Std.U8 N) 128#usize) (first : Std.U32)
  (adr : address.Adrs) :
  Result (Array (Array Std.U8 N) 128#usize)
  := do
  loop
    (fun (iter1, nodes1) => fors.arm.subtree_loop1_loop0.body a a1 a2 first adr
      iter1 nodes1)
    (iter, nodes)

/-- Extracted native Arm FORS subtree operation. -/
@[rust_loop_body]
def fors.arm.subtree_loop1.body
  (enabled : Bool) {N : Std.Usize} (index : Std.U32) (height : Std.U32) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize)
  (adrs : address.Adrs) (n : Std.Usize)
  (iter : core.ops.range.RangeInclusive Std.U32)
  (nodes : Array (Array Std.U8 N) 128#usize) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.U32) × (Array (Array
    Std.U8 N) 128#usize)) (Array (Array Std.U8 N) 128#usize))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepU32 iter
  match o with
  | none => ok (done nodes)
  | some level =>
    let i ← height - level
    let first ← index <<< i
    let adr ← address.Adrs.with_word2 adrs level
    let count ← n >>> level
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut nodes)
    let (done1, s1) ← parentSliceAt 128#usize enabled a2 adr first s count
    let nodes1 := to_slice_mut_back s1
    let nodes2 ←
      fors.arm.subtree_loop1_loop0 { start := done1, «end» := count } a a1 a2
        nodes1 first adr
    ok (cont (iter1, nodes2))

/-- Extracted native Arm FORS subtree operation. -/
@[rust_loop]
def fors.arm.subtree_loop1
  (enabled : Bool) {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.U32)
  (index : Std.U32) (height : Std.U32) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize)
  (adrs : address.Adrs) (n : Std.Usize)
  (nodes : Array (Array Std.U8 N) 128#usize) :
  Result (Array (Array Std.U8 N) 128#usize)
  := do
  loop
    (fun (iter1, nodes1) => fors.arm.subtree_loop1.body enabled index height a a1 a2
      adrs n iter1 nodes1)
    (iter, nodes)

/-- Extracted native Arm FORS subtree operation. -/
def fors.arm.subtree
  (enabled : Bool) {N : Std.Usize} (sk_seed : Array Std.U8 N) (index : Std.U32)
  (height : Std.U32) (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let n ← 1#usize <<< height
  if N = 16#usize
  then
    let sk16 := Array.repeat 16#usize 0#u8
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut sk16)
    let s1 ← lift (Array.to_slice sk_seed)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let a := Array.repeat 16#usize 0#u8
    let nodes := Array.repeat 128#usize a
    let sk161 := to_slice_mut_back s2
    let i ← index <<< height
    let (s3, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 16#usize)))
        nodes { «end» := n }
    let s4 ← fillLeaves seed.state sk161 adrs i s3
    let iter ← core.ops.range.RangeInclusive.new 1#u32 height
    let nodes1 := index_mut_back s4
    let nodes2 ←
      fors.arm.subtree_loop0 iter index height seed.state adrs n nodes1
    let out := Array.repeat N 0#u8
    let (s5, to_slice_mut_back1) ← lift (Array.to_slice_mut out)
    let a1 ← Array.index_usize nodes2 0#usize
    let s6 ← lift (Array.to_slice a1)
    let s7 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s5 s6
    ok (to_slice_mut_back1 s7)
  else
    let a := Array.repeat N 0#u8
    let nodes := Array.repeat 128#usize a
    let i ← index <<< height
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) nodes
        { «end» := n }
    let s1 ← fillLeaves seed.state sk_seed adrs i s
    let iter ← core.ops.range.RangeInclusive.new 1#u32 height
    let nodes1 := index_mut_back s1
    let nodes2 ←
      fors.arm.subtree_loop1 enabled iter index height seed.pk_seed seed.state
        seed.state512 adrs n nodes1
    Array.index_usize nodes2 0#usize

/-- The FORS tail and XMSS tail call the same scalar hash and perform the same
in-place reads and writes on their respective array sizes. -/
theorem shared_tail {N} (it : core.ops.range.Range Usize) (seed : hash.Seed N)
    (roots : Nodes N 128#usize) (first : U32) (a : address.Adrs) :
    fors.arm.subtree_loop1_loop0 it seed.pk_seed seed.state seed.state512 roots first a =
      ArmXmss.xmss.arm.batch_root_512_loop0_loop0 it seed.pk_seed seed.state seed.state512 roots a first := rfl

end slhdsa.ArmForsTree
