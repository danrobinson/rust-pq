import Slhdsa.Proofs.Sha512Core
open Aeneas Aeneas.Std Result

/-! `sha512::compress`, as built by default: the portable code.

With `CompressTop.lean` and `ChainTop.lean`, one of the proof files that depend
on the build. In `lean-hw`, which holds the translation of the crate built with
`hw-sha2`, it has a counterpart that also goes through the hardware backend. -/

namespace slhdsa
namespace S512
open Spec.SHA512

@[step]
theorem compress_spec (state : Array U64 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 128 ≤ data.length) :
    sha512.compress state data off ⦃ r =>
      wv r.val = compress (wv state.val) (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold sha512.compress
  exact compress_portable_spec state data off hoff

end S512

end slhdsa
