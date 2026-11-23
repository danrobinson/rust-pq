import Slhdsa.Proofs.Sha512Core
import Slhdsa.Proofs.Hw512.Compress
import Slhdsa.Proofs.Hw512.Guard
open Aeneas Aeneas.Std Result

/-! `sha512::compress`, as built with `hw-sha2`: the hardware backend if the
processor has the SHA-512 instructions, the portable code otherwise. The
statement is the one of the default build (`lean/Slhdsa/Proofs/Compress512Top.lean`).

The kernel's wrappers fail without the instructions (`Slhdsa/FunsExternal.lean`),
so the proof of the first branch needs `Arm.haveSha512 = true`; it takes it
from the test `available()` that guards the branch. Without the instructions
the kernel fails (`compress_block512_undef` in `Hw512/Guard.lean`). -/

namespace slhdsa
open Spec.SHA512

/-- Whenever the hardware backend returns a state, it is the SHA-512
compression function of FIPS 180-4 on the block at `off`. -/
theorem hw_compress512_spec (state : Array U64 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 128 ≤ data.length) :
    sha512.hw.compress state data off ⦃ o => ∀ out, o = some out →
      S512.wv out.val = compress (S512.wv state.val) (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold sha512.hw.compress sha512.hw.arm.available
  simp only [bind_ok]
  split
  · rename_i hw
    step*
    let* ⟨ a, a_post ⟩ ← hw_compress_block512_spec
    intro out hout
    simp only [Option.some.injEq] at hout
    subst hout
    rw [a_post]
    have hv : (Array.from_slice (Array.repeat 128#usize 0#u8) s1).val = s1.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    simp only [to_slice_mut_back_post, s2_post, hv, s1_post, i_post, List.slice]
    simp
  · simp

namespace S512

@[step]
theorem compress_spec (state : Array U64 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 128 ≤ data.length) :
    sha512.compress state data off ⦃ r =>
      wv r.val = compress (wv state.val) (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold sha512.compress
  let* ⟨ o, o_post ⟩ ← hw_compress512_spec
  cases o with
  | none => exact compress_portable_spec state data off hoff
  | some out => simpa using o_post out rfl

end S512

end slhdsa

namespace slhdsa

/-- `sha256::hw_active` reports the answer of the SHA-256 feature test. -/
theorem sha256_hw_active_eq : sha256.hw_active = ok Arm.haveSha2 := rfl

/-- `sha512::hw_active` reports the answer of the SHA-512 feature test. -/
theorem sha512_hw_active_eq : sha512.hw_active = ok Arm.haveSha512 := rfl

end slhdsa
