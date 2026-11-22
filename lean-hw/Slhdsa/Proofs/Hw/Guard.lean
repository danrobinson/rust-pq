import Slhdsa.Proofs.Hw.Wrappers
open Aeneas Aeneas.Std Result

/-! Without the instructions the kernels fail.

The wrappers of `Slhdsa/FunsExternal.lean` fail when `Arm.haveSha2 = false`
(`wr_*_undef`), so do both kernels of the hardware backend, from their first
instruction on: `compress_block` at its first load, `chain_all` at the `zero`
it starts with, whatever the arguments. No specification of either can hold
then. So the proofs of `sha256::compress` and `hash::chain_blocks`
(`CompressTop.lean`, `ChainTop.lean`) can only go through a kernel on a path
where `Arm.haveSha2 = true` is known, and in the code the only source of that
fact is the answer of `available()`. -/

namespace slhdsa

section
variable (hw : Arm.haveSha2 = false)
include hw

/-- The single-block kernel fails without the instructions. -/
theorem compress_block_undef (state : Array U32 8#usize) (block : Array U8 64#usize) :
    sha256.hw.compress_block state block = fail .undef := by
  simp [sha256.hw.compress_block, wr_load_words_undef hw, lift]

/-- The four-lane chain kernel fails without the instructions. -/
theorem chain_all_undef (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (start «end» : Slice U32) :
    sha256.hw.chain_all state blocks start «end» = fail .undef := by
  simp [sha256.hw.chain_all, wr_zero_undef hw]

/-- So no postcondition holds of the single-block kernel. -/
theorem compress_block_no_spec (state : Array U32 8#usize) (block : Array U8 64#usize)
    (P : Array U32 8#usize → Prop) : ¬ sha256.hw.compress_block state block ⦃ r => P r ⦄ := by
  rw [compress_block_undef hw]
  simp

/-- Nor of the chain kernel. -/
theorem chain_all_no_spec (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (start «end» : Slice U32) (P : Slice (Array U8 64#usize) → Prop) :
    ¬ sha256.hw.chain_all state blocks start «end» ⦃ r => P r ⦄ := by
  rw [chain_all_undef hw]
  simp

end

end slhdsa
