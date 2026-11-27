import Parallel.XmssTicketHosted
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelXmssTicket
def chunk
  (p : params.Params) (j : Std.Usize) (index : Std.U32) (h : Std.U32)
  (c : Std.Usize) (xmss_slot_count : Std.Usize) :
  Result (Std.Usize × Std.U32 × Std.U32 × Std.U32 × Std.Usize × Std.U16 ×
    Std.U32 × Std.U32 × Std.Usize)
  := do
  let xmss_target ← if p.hp >= 6#u32
                      then ok 3#u32
                      else ok 2#u32
  let i ← index >>> h
  let root_idx ← lift (i ^^^ 1#u32)
  let split ← lift (core.num.U32.saturating_sub h xmss_target)
  let sub_h ← h - split
  let chunks ← 1#usize <<< split
  let xmss_slot_count1 ← xmss_slot_count + chunks
  let i1 ← lift (UScalar.cast .U16 j)
  let i2 ← root_idx <<< split
  let i3 ← lift (UScalar.cast .U32 c)
  let i4 ← i2 + i3
  let i5 ← xmss_slot_count + c
  ok (xmss_slot_count1, root_idx, split, h, xmss_slot_count, i1, i4, sub_h, i5)
end slhdsa.ParallelXmssTicket
