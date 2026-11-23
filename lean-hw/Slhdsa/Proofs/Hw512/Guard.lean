import Slhdsa.Proofs.Hw512.Wrappers
open Aeneas Aeneas.Std Result

/-! Without the SHA-512 instructions the SHA-512 kernel fails.

The wrappers of `rust/src/sha512.rs`, module `hw::arm`, fail when
`Arm.haveSha512 = false` (`wr512_*_undef`), so does `compress_block`, from its
first load on, whatever the arguments. No specification of it can hold then.
So the proof of `sha512::compress` (`Compress512Top.lean`) can only go through
the kernel on a path where `Arm.haveSha512 = true` is known, and in the code
the only source of that fact is the answer of `sha512::hw::arm::available()`. -/

namespace slhdsa

section
variable (hw : Arm.haveSha512 = false)
include hw

/-- The SHA-512 kernel fails without the instructions. -/
theorem compress_block512_undef (state : Array U64 8#usize) (block : Array U8 128#usize) :
    sha512.hw.compress_block state block = fail .undef := by
  simp [sha512.hw.compress_block, wr512_load_words_undef hw, lift]

/-- So no postcondition holds of it. -/
theorem compress_block512_no_spec (state : Array U64 8#usize) (block : Array U8 128#usize)
    (P : Array U64 8#usize → Prop) : ¬ sha512.hw.compress_block state block ⦃ r => P r ⦄ := by
  rw [compress_block512_undef hw]
  simp

end

end slhdsa
