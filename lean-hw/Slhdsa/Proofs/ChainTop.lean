import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Hw.Chain
import Slhdsa.Proofs.Hw.Guard
open Aeneas Aeneas.Std Result

/-! `hash::chain_blocks`, as built with `hw-sha2`: the hardware backend if the
processor has the instructions and the arguments are in range, the portable
loops otherwise. The statement is the one of the default build
(`lean/Slhdsa/Proofs/ChainTop.lean`).

The kernel's wrappers fail without the instructions (`Slhdsa/FunsExternal.lean`,
and `chain_all_undef` in `Hw/Guard.lean`), so the kernel's specification needs
`Arm.haveSha2 = true`; the proof takes it, as `hb`, from the answer of the test
`available()` in the branch that calls the kernel. -/

namespace slhdsa

/-- `chain_blocks`: block `i` takes the steps `start[i]`, …, `end[i] − 1`. -/
@[step]
theorem chain_blocks_spec (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    hash.chain_blocks state blocks start «end» ⦃ r =>
      r.length = blocks.length ∧ ∀ i, i < blocks.length → bytes (r.val[i]!).val =
        runBlock (wv state.val) (bytes (blocks.val[i]!).val) (start.val[i]!).val («end».val[i]!).val ⦄ := by
  unfold hash.chain_blocks sha256.hw.chain_blocks sha256.hw.arm.available
  cases hb : Arm.haveSha2
  · simpa using chain_blocks_portable_spec state blocks start «end» hs he
  · -- `available()` said yes: `hb : Arm.haveSha2 = true`.
    have h1 : ¬ (Slice.len start < Slice.len blocks) := by scalar_tac
    have h2 : ¬ (Slice.len «end» < Slice.len blocks) := by scalar_tac
    obtain ⟨r, hr, hp⟩ := spec_imp_exists (hw_chain_all_spec hb state blocks start «end» hs he)
    simpa [h1, h2, hr] using hp

end slhdsa
