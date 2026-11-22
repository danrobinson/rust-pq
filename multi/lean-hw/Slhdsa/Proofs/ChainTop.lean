import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Hw.Chain
import Slhdsa.Proofs.Hw.Guard
open Aeneas Aeneas.Std Result

/-! `hash::chain_blocks::<N>`, as built with `hw-sha2`: the hardware backend if
`N` is one of 16, 24, 32, the processor has the instructions and the arguments
are in range; the portable loops otherwise. The statement is the one of the
default build (`../lean/Slhdsa/Proofs/ChainTop.lean`), word for word.

The kernel's wrappers fail without the instructions (`Slhdsa/FunsExternal.lean`,
and `chain_all_undef` in `Hw/Guard.lean`), so the kernel's specification needs
`Arm.haveSha2 = true`; the proof takes it, as `hb`, from the answer of the test
`available()` in the branch that calls the kernel. The kernel is proved for the
three hash lengths it is entered with (`KN`); for any other `N` the code does
not enter it. -/

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
  unfold hash.chain_blocks sha256.hw.chain_blocks sha256.hw.arm.available
  have h1 : ¬ (Slice.len start < Slice.len blocks) := by scalar_tac
  have h2 : ¬ (Slice.len «end» < Slice.len blocks) := by scalar_tac
  cases hb : Arm.haveSha2
  · simpa using chain_blocks_portable_spec N hN state blocks start «end» hs he
  · -- `available()` said yes: `hb : Arm.haveSha2 = true`.
    by_cases hK : N = 16#usize ∨ N = 24#usize ∨ N = 32#usize
    · have hKN : KN N.val := by
        rcases hK with h | h | h <;> subst h <;> simp [KN]
      obtain ⟨r, hr, hp⟩ :=
        spec_imp_exists (hw_chain_all_spec hb N hKN state blocks start «end» hs he)
      rcases hK with h | h | h <;> subst h <;> simpa [h1, h2, hr] using hp
    · simp only [not_or] at hK
      obtain ⟨k1, k2, k3⟩ := hK
      simpa [k1, k2, k3] using chain_blocks_portable_spec N hN state blocks start «end» hs he

end slhdsa
