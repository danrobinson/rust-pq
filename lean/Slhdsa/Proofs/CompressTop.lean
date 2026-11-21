import Slhdsa.Proofs.Sha256Core
open Aeneas Aeneas.Std Result

/-! `sha256::compress`, as built by default: the portable code.

This file and `ChainTop.lean` are the only proof files that depend on the
build. In `lean-hw`, which holds the translation of the crate built with
`hw-sha2`, they have counterparts that also go through the hardware backend;
every other proof file there is this directory's, linked. -/

namespace slhdsa
open Spec.SHA256

@[step]
theorem compress_spec (state : Array U32 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 64 ≤ data.length) :
    sha256.compress state data off ⦃ r =>
      wv r.val = compress (wv state.val) (((bytes data.val).drop off.val).take 64) ⦄ := by
  unfold sha256.compress
  exact compress_portable_spec state data off hoff

end slhdsa
