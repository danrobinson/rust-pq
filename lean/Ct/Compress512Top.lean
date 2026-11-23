import Ct.Sha512Core

/-!
# Constant time: `sha512::compress`, as built by default

The portable code. With `Ct/CompressTop.lean` and `Ct/ChainTop.lean`, one of the constant-time
proof files whose content depends on the build; `../lean-hw/Ct` has its own.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Sha512

open slhdsa_leak

@[ct_rel] theorem compress (state state' : Array U64 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha512.compress state data off) (sha512.compress state' data' off)
      (fun _ _ => True) := by
  unfold sha512.compress
  exact compress_portable state state' data data' off h

end Ct.Sha512
