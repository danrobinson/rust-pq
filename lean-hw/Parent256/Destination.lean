import Parent256.InPlace
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Parent

def destination (rows : Rows) (start count : Usize) := do
  let stop ← start + 16#usize
  let limit ← lift (core.cmp.impls.OrdUsize.min count stop)
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 16#usize))
    rows (⟨start,limit⟩ : core.ops.range.Range Usize)

theorem destination_spec (rows : Rows) (start count : Usize) (le : start.val ≤ count.val)
    (valid : count.val ≤ rows.length) (size : start.val+16 ≤ Usize.max) :
    destination rows start count ⦃ dst back =>
      dst.length = min (count.val-start.val) 16 ∧
      ∀ r, (back r).val = rows.val.setSlice! start.val r.val ⦄ := by
  unfold destination
  step as ⟨stop,hstop⟩
  simp only [lift,bind_tc_eq,bind_ok]
  have val : (core.cmp.impls.OrdUsize.min count stop).val = min count.val stop.val := by simp
  step as ⟨dst,back,hd,hl,hb⟩
  refine ⟨by omega,fun r => ?_⟩
  simp only [hb,Slice.setSlice!_val]

def finishBatch (base : Array Reg 16#usize) (iv pre : Array Reg 8#usize) (idx : Reg)
    (rows : Rows) (stride : Reg) (start count : Usize) (mask : U16) := do
  let w ← prepare base idx rows stride start mask
  let d ← TreeRust.sha256.x86.avx512.compress iv pre w
  let (dst,back) ← destination rows start count
  let r ← TreeRust.sha256.x86.avx512.write_words d dst
  ok (back r)

theorem finish_eq (base : Array Reg 16#usize) (iv pre : Array Reg 8#usize) (idx : Reg)
    (rows : Rows) (stride : Reg) (start count : Usize) (mask : U16)
    (dst : Rows) (back : Rows → Rows) (okDest : destination rows start count = ok (dst,back)) :
    finishBatch base iv pre idx rows stride start count mask =
      (do let r ← hashBatch base iv pre idx rows stride start mask dst; ok (back r)) := by
  unfold finishBatch hashBatch
  simp only [bind_tc_eq,okDest,bind_ok,Std.bind_assoc]

end slhdsa.X86.Parent
