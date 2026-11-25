import Slhdsa.Proofs.Xmss

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ArmXmss

/-- Extracted scalar remainder of the native Arm XMSS parent pass. -/
@[rust_loop_body]
def xmss.arm.batch_root_512_loop0_loop0.body
  {N cap : Std.Usize} (a : Array Std.U8 N) (a1 : Array Std.U32 8#usize)
  (a2 : Array Std.U64 8#usize) (adr : address.Adrs) (level_first : Std.U32)
  (iter : core.ops.range.Range Std.Usize)
  (roots : Array (Array Std.U8 N) cap) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) cap)) (Array (Array Std.U8 N) cap))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done roots)
  | some j =>
    let i ← lift (UScalar.cast .U32 j)
    let i1 ← level_first + i
    let a3 ← address.Adrs.with_word3 adr i1
    let i2 ← 2#usize * j
    let a4 ← Array.index_usize roots i2
    let i3 ← i2 + 1#usize
    let a5 ← Array.index_usize roots i3
    let a6 ←
      xmss.hash2 { pk_seed := a, state := a1, state512 := a2 } a3 a4 a5
    let a7 ← Array.update roots j a6
    ok (cont (iter1, a7))

/-- Extracted scalar remainder of the native Arm XMSS parent pass. -/
@[rust_loop]
def xmss.arm.batch_root_512_loop0_loop0
  {N cap : Std.Usize} (iter : core.ops.range.Range Std.Usize) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize)
  (roots : Array (Array Std.U8 N) cap) (adr : address.Adrs)
  (level_first : Std.U32) :
  Result (Array (Array Std.U8 N) cap)
  := do
  loop
    (fun (iter1, roots1) => xmss.arm.batch_root_512_loop0_loop0.body a a1 a2
      adr level_first iter1 roots1)
    (iter, roots)

end slhdsa.ArmXmss
