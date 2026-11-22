import Ct.Sha256Core

/-!
# Constant time: `sha256::compress`, as built by default

The portable code. This file and `Ct/ChainTop.lean` are the only constant-time proof files
whose content depends on the build (with the generated `Ct/Funs.lean`, the build's part of the
model `Ct/ModelBuild.lean`, and the root `Ct.lean`). In `lean-hw`, which holds the translation
of the crate built with `hw-sha2`, they have counterparts with the same statements that also
go through the hardware backend; every other file there is this directory's, linked.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Sha256

open slhdsa_leak

@[ct_rel] theorem compress (state state' : Array U32 8#usize) (data data' : Slice U8)
    (off : Usize) (h : data.length = data'.length) :
    Rel (sha256.compress state data off) (sha256.compress state' data' off)
      (fun _ _ => True) := by
  unfold sha256.compress
  exact compress_portable state state' data data' off h

end Ct.Sha256
