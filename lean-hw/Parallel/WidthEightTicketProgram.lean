import Parallel.SignTicket
import Shakebatch.WidthEightOuterHosted
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket

noncomputable def ticket (host : Platform) (p : params.Params)
  {N : Std.Usize} (layers : alloc.vec.Vec (address.Adrs × Std.U32))
  (roots : alloc.vec.Vec (Array Std.U8 N)) (j : Std.Usize)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let (addr, index) ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (address.Adrs ×
      Std.U32)) layers j
  let a ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
      N)) roots j
  let a1 ← address.Adrs.with_type addr address.WOTS_HASH
  let a2 ← address.Adrs.with_keypair a1 index
  @Fused.Outer.shake.wots.wots_sign (host.outer p) N a sk seed a2

end slhdsa.WidthEight.Ticket
