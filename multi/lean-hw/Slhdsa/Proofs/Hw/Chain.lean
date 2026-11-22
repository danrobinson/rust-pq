import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Hw.Rounds
import Slhdsa.Proofs.Hw.ChainAll
open Aeneas Aeneas.Std Result

/-! The hardware chain kernel, `sha256::hw::chain_all::<N>`, does what the
portable loops of `hash::chain_blocks_portable::<N>` do, for each hash length
`N` ∈ {16, 24, 32} (`KN`), given the instruction model in `Arm.lean`, on a
processor with the instructions (`hw : Arm.haveSha2 = true`, assumed by every
statement in `Hw/Chain*.lean` that runs a wrapper).

The counterpart of `../../lean-hw/Slhdsa/Proofs/Hw/Chain.lean`, whose kernel
is the N = 16 one. -/

namespace slhdsa

theorem hw_chain_all_spec (hw : Arm.haveSha2 = true) (N : Usize) (hN : KN N.val)
    (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    sha256.hw.chain_all N state blocks start «end» ⦃ r =>
      r.length = blocks.length ∧ ∀ i, i < blocks.length → bytes (r.val[i]!).val =
        runBlock N.val (wv state.val) (bytes (blocks.val[i]!).val) (start.val[i]!).val
          («end».val[i]!).val ⦄ := by
  unfold sha256.hw.chain_all
  step*
  apply main_loop_spec hw N hN state blocks start «end» hs he
  refine ⟨by simp, by simp, rfl, fun h => by simp at h, by simp, by simp, fun i _ _ => rfl,
    fun i _ hi => absurd hi (by simp)⟩

end slhdsa
