import Ct.Check

/-!
# Tests of the leakage-model checks for this tree's `hw-sha2` build

The union of the single-set tree's `lean-hw/Ct/CheckTestBuild.lean` (git `26aa3d8`) (the intrinsic wrappers) and
this tree's portable `../lean/Ct/CheckTestBuild.lean` (`Slice.index_mut`, 64/128-bit division),
both copied unchanged: the names of the intrinsic wrappers in the generated text resolve to
their instrumented versions of `Ct/ModelBuild.lean` (inside `def sha256.hw.f` the current
namespace is `slhdsa_leak.sha256.hw`), as does `core.slice.index.Slice.index_mut`, and the
checker rejects the un-instrumented ones.
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

-- the SHA-512 wrappers (2026-11-22)
namespace sha512.hw
#ct_resolves sha512.hw.arm.available
#ct_resolves sha512.hw.arm.add
#ct_resolves sha512.hw.arm.ext1
#ct_resolves sha512.hw.arm.sha512h
#ct_resolves sha512.hw.arm.sha512h2
#ct_resolves sha512.hw.arm.sha512su0
#ct_resolves sha512.hw.arm.sha512su1
#ct_resolves sha512.hw.arm.store_words
#ct_resolves sha512.hw.arm.load_words
#ct_resolves sha512.hw.arm.load_be
end sha512.hw

-- this tree's portable build

#ct_resolves core.slice.index.Slice.index_mut

namespace hash
-- inside `def hash.f` the current namespace is `slhdsa_leak.hash`
#ct_resolves core.slice.index.Slice.index_mut
end hash

/-- A mutable sub-slice of a slice emits its range and the slice's length. -/
example (s : Aeneas.Std.Slice Std.U8) (a b : Std.Usize) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
      { start := a, «end» := b } =
    Ct.Leak.prim [.range a.val b.val s.length]
      (Aeneas.Std.core.slice.index.Slice.index_mut
        (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
        { start := a, «end» := b }) := rfl

/-- `/` on 64-bit and 128-bit integers is the leaking division. -/
example (x y : Std.U64) : (x / y) = Ct.Leak.prim [.div x.val y.val] (UScalar.div x y) := rfl
example (x y : Std.U128) : (x / y) = Ct.Leak.prim [.div x.val y.val] (UScalar.div x y) := rfl

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

def badLoad512 (s : Aeneas.Std.Slice Std.U64) : Ct.Leak core.core_arch.arm_shared.neon.uint64x2_t := do
  let v ← slhdsa.sha512.hw.arm.load_words s 0#usize
  Ct.Leak.pure v
#ct_expect_reject badLoad512 slhdsa.sha512.hw.arm.load_words

def badLoadBe512 (s : Aeneas.Std.Slice Std.U8) : Ct.Leak core.core_arch.arm_shared.neon.uint64x2_t := do
  let v ← slhdsa.sha512.hw.arm.load_be s 0#usize
  Ct.Leak.pure v
#ct_expect_reject badLoadBe512 slhdsa.sha512.hw.arm.load_be

def badAvailable512 : Ct.Leak Bool := do
  let b ← slhdsa.sha512.hw.arm.available
  Ct.Leak.pure b
#ct_expect_reject badAvailable512 slhdsa.sha512.hw.arm.available

def badAssert (b : Bool) : Ct.Leak Unit := do
  Aeneas.Std.massert (b = true)
#ct_expect_reject badAssert Aeneas.Std.massert

-- this tree's portable build

def badSliceIndexMut (s : Aeneas.Std.Slice Std.U8) :
    Ct.Leak (Aeneas.Std.Slice Std.U8 × (Aeneas.Std.Slice Std.U8 → Aeneas.Std.Slice Std.U8)) := do
  let r ← Aeneas.Std.core.slice.index.Slice.index_mut
    (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
    { start := 0#usize, «end» := 1#usize }
  Ct.Leak.pure r
#ct_expect_reject badSliceIndexMut Aeneas.Std.core.slice.index.Slice.index_mut

def badDiv128 (x y : Std.U128) : Ct.Leak Std.U128 := do
  let z ← Aeneas.Std.UScalar.div x y
  Ct.Leak.pure z
#ct_expect_reject badDiv128 Aeneas.Std.UScalar.div

end Ct.CheckTestBuild
