import Ct.Check

/-!
# Tests of the leakage-model checks for the `hw-sha2` build

The names of the intrinsic wrappers in the generated text resolve to their instrumented
versions of `Ct/ModelBuild.lean` (inside `def sha256.hw.f` the current namespace is
`slhdsa_leak.sha256.hw`), and the checker rejects the un-instrumented wrappers of
`Slhdsa/FunsExternal.lean`.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa

namespace slhdsa_leak

#ct_resolves massert
#ct_resolves core.core_arch.arm_shared.neon.uint32x4_t.Insts.CoreCloneClone.clone

namespace sha256.hw
#ct_resolves sha256.hw.arm.available
#ct_resolves sha256.hw.arm.zero
#ct_resolves sha256.hw.arm.pair
#ct_resolves sha256.hw.arm.add
#ct_resolves sha256.hw.arm.or
#ct_resolves sha256.hw.arm.and
#ct_resolves sha256.hw.arm.shr16
#ct_resolves sha256.hw.arm.shl16
#ct_resolves sha256.hw.arm.ext2
#ct_resolves sha256.hw.arm.ext3
#ct_resolves sha256.hw.arm.sha256h
#ct_resolves sha256.hw.arm.sha256h2
#ct_resolves sha256.hw.arm.sha256su0
#ct_resolves sha256.hw.arm.sha256su1
#ct_resolves sha256.hw.arm.store_words
#ct_resolves sha256.hw.arm.load_words
#ct_resolves sha256.hw.arm.load_be
#ct_resolves sha256.hw.arm.store_be
#ct_resolves massert
end sha256.hw

namespace sha256
#ct_resolves sha256.hw.arm.available
end sha256

end slhdsa_leak

namespace Ct.CheckTestBuild

/-! Positive controls: the wrappers of `Slhdsa/FunsExternal.lean`, lifted without events. -/

def badLoad (s : Aeneas.Std.Slice Std.U32) : Ct.Leak core.core_arch.arm_shared.neon.uint32x4_t := do
  let v ← slhdsa.sha256.hw.arm.load_words s 0#usize
  Ct.Leak.pure v
#ct_expect_reject badLoad slhdsa.sha256.hw.arm.load_words

def badStore (s : Aeneas.Std.Slice Std.U8) (v : core.core_arch.arm_shared.neon.uint32x4_t) :
    Ct.Leak (Aeneas.Std.Slice Std.U8) := do
  let r ← slhdsa.sha256.hw.arm.store_be s 0#usize v
  Ct.Leak.pure r
#ct_expect_reject badStore slhdsa.sha256.hw.arm.store_be

def badAvailable : Ct.Leak Bool := do
  let b ← slhdsa.sha256.hw.arm.available
  Ct.Leak.pure b
#ct_expect_reject badAvailable slhdsa.sha256.hw.arm.available

def badAssert (b : Bool) : Ct.Leak Unit := do
  Aeneas.Std.massert (b = true)
#ct_expect_reject badAssert Aeneas.Std.massert

end Ct.CheckTestBuild
