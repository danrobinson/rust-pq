import Slhdsa.Proofs.Sha256Core
import Slhdsa.Proofs.Hw.Compress
import Slhdsa.Proofs.Hw.Guard
open Aeneas Aeneas.Std Result

/-! `sha256::compress`, as built with `hw-sha2`: the hardware backend if the
processor has the instructions, the portable code otherwise. The statement is
the one of the default build (`lean/Slhdsa/Proofs/CompressTop.lean`).

The kernel's wrappers fail without the instructions (`Slhdsa/FunsExternal.lean`),
so the proof of the first branch needs `Arm.haveSha2 = true`; it takes it from
the test `available()` that guards the branch. Without the instructions the
kernel fails (`compress_block_undef` in `Hw/Guard.lean`). -/

namespace slhdsa
open Spec.SHA256

theorem hw_compress_spec (state : Array U32 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 64 ≤ data.length) :
    sha256.hw.compress state data off ⦃ o => ∀ out, o = some out →
      wv out.val = compress (wv state.val) (((bytes data.val).drop off.val).take 64) ⦄ := by
  unfold sha256.hw.compress sha256.hw.arm.available
  simp only [bind_ok]
  split
  · -- The processor has the instructions: the answer of `available`, which the
    -- wrappers in the kernel need.
    rename_i hw
    step*
    let* ⟨ a, a_post ⟩ ← hw_compress_block_spec
    intro out hout
    simp only [Option.some.injEq] at hout
    subst hout
    rw [a_post]
    have hv : (Array.from_slice (Array.repeat 64#usize 0#u8) s1).val = s1.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    simp only [to_slice_mut_back_post, s2_post, hv, s1_post, i_post, List.slice]
    simp
  · simp

@[step]
theorem compress_spec (state : Array U32 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 64 ≤ data.length) :
    sha256.compress state data off ⦃ r =>
      wv r.val = compress (wv state.val) (((bytes data.val).drop off.val).take 64) ⦄ := by
  unfold sha256.compress
  let* ⟨ o, o_post ⟩ ← hw_compress_spec
  cases o with
  | none => exact compress_portable_spec state data off hoff
  | some out => simpa using o_post out rfl

end slhdsa
