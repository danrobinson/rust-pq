import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result

/-! `hash::chain_blocks`, as built by default: the portable loops. This file
and `CompressTop.lean` are the only proof files that depend on the build; the
`hw-sha2` package has its own versions, which also go through the hardware
backend. -/

namespace slhdsa

/-- `chain_blocks`: block `i` takes the steps `start[i]`, …, `end[i] − 1`. -/
@[step]
theorem chain_blocks_spec (N : Usize) (hN : N.val ≤ 32) (state : Array U32 8#usize)
    (blocks : Slice (Array U8 64#usize)) (start «end» : Slice U32)
    (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    hash.chain_blocks N state blocks start «end» ⦃ r =>
      r.length = blocks.length ∧ ∀ i, i < blocks.length → bytes (r.val[i]!).val =
        runBlock N.val (wv state.val) (bytes (blocks.val[i]!).val) (start.val[i]!).val
          («end».val[i]!).val ⦄ := by
  unfold hash.chain_blocks
  exact chain_blocks_portable_spec N hN state blocks start «end» hs he

end slhdsa
