-- [slhdsa]: external functions.
-- Hand-written: the meaning of the functions Aeneas does not translate.
module
public import Aeneas
public import Arm
public import Slhdsa.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-!
# The intrinsic wrappers of `rust/src/sha256.rs`, module `hw::arm`

Aeneas translates the whole crate as built with `hw-sha2`, except the
functions of that module, each of which is one to three intrinsics. This file
says what each of them does, in terms of the instruction model in `Arm.lean`.
It is the trusted part of the proofs about the `hw-sha2` build: the theorems
hold if these definitions describe the Rust functions. `scripts/extract-hw.sh`
checks that every function Aeneas left out has a definition here.

Every wrapper but `available` is compiled with the `neon` and `sha2` features
enabled (`target_feature(enable = "neon,sha2")`, or the target has them
unconditionally), and calling it on a processor without them is undefined
behaviour. So each of those seventeen definitions begins with
`if Arm.haveSha2 then … else fail .undef`: on a processor without the
instructions the call is a failure, never a result. Since every theorem about
the crate says that the functions it covers succeed, a proof can only go
through the kernel on the branch where `available` (which returns
`Arm.haveSha2`) said yes. When the features are present, each definition is
what follows the `then`.

A wrapper that touches memory checks its bounds and panics outside them, and
so does its definition. Vectors in memory are little-endian, so element `i`
of a vector loaded from words is word `i`.
-/

open slhdsa

namespace slhdsa

/-- [core::core_arch::arm_shared::neon::{impl core::clone::Clone for
core::core_arch::arm_shared::neon::uint32x4_t}::clone]: a copy. -/
@[rust_fun
  "core::core_arch::arm_shared::neon::{core::clone::Clone<core::core_arch::arm_shared::neon::uint32x4_t>}::clone"]
def core.core_arch.arm_shared.neon.uint32x4_t.Insts.CoreCloneClone.clone
  (v : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t := ok v

/-- [core::panicking::panic_bounds_check]: a panic. -/
@[rust_fun "core::panicking::panic_bounds_check"]
def core.panicking.panic_bounds_check (_ _ : Std.Usize) : Result Never := fail .panic

/-- [slhdsa::sha256::hw::arm::available]: `is_aarch64_feature_detected!` for
`neon` and `sha2`. The only wrapper without the features, and the only place
`Arm.haveSha2` reaches the translated code. -/
def sha256.hw.arm.available : Result Bool := ok Arm.haveSha2

/-- [slhdsa::sha256::hw::arm::zero]: `vdupq_n_u32(0)`. -/
def sha256.hw.arm.zero : Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (⟨0, 0, 0, 0⟩ : Arm.V) else fail .undef

/-- [slhdsa::sha256::hw::arm::pair]: `[a, b, 0, 0]`, by two `vsetq_lane_u32`
on a zero vector. -/
def sha256.hw.arm.pair (a b : Std.U32) : Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (⟨a.bv, b.bv, 0, 0⟩ : Arm.V) else fail .undef

/-- [slhdsa::sha256::hw::arm::load_words]: `vld1q_u32` at `w[at..at + 4]`,
after `assert!(w.len() >= 4 && at <= w.len() - 4)`. -/
def sha256.hw.arm.load_words (w : Slice Std.U32) (at' : Std.Usize) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then
    if 4 ≤ w.length ∧ at'.val ≤ w.length - 4 then
      ok (⟨(w.val[at'.val]!).bv, (w.val[at'.val + 1]!).bv, (w.val[at'.val + 2]!).bv,
        (w.val[at'.val + 3]!).bv⟩ : Arm.V)
    else fail .panic
  else fail .undef

/-- [slhdsa::sha256::hw::arm::store_words]: two `vst1q_u32`, the elements of
`a` then those of `e`. -/
def sha256.hw.arm.store_words (a e : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result (Array Std.U32 8#usize) :=
  let a : Arm.V := a
  let e : Arm.V := e
  if Arm.haveSha2 then
    ok (Array.make 8#usize [⟨a.e0⟩, ⟨a.e1⟩, ⟨a.e2⟩, ⟨a.e3⟩, ⟨e.e0⟩, ⟨e.e1⟩, ⟨e.e2⟩, ⟨e.e3⟩])
  else fail .undef

/-- [slhdsa::sha256::hw::arm::load_be]: `vld1q_u8` at `b[at..at + 16]`, then
`vrev32q_u8`, viewed as four words, after
`assert!(b.len() >= 16 && at <= b.len() - 16)`. -/
def sha256.hw.arm.load_be (b : Slice Std.U8) (at' : Std.Usize) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then
    if 16 ≤ b.length ∧ at'.val ≤ b.length - 16 then
      let g (i : Nat) : BitVec 8 := (b.val[at'.val + i]!).bv
      ok (⟨Arm.beWord (g 0) (g 1) (g 2) (g 3), Arm.beWord (g 4) (g 5) (g 6) (g 7),
        Arm.beWord (g 8) (g 9) (g 10) (g 11), Arm.beWord (g 12) (g 13) (g 14) (g 15)⟩ : Arm.V)
    else fail .panic
  else fail .undef

/-- The sixteen bytes `store_be` writes. -/
def sha256.hw.arm.be_bytes (v : Arm.V) : List Std.U8 :=
  (Arm.beBytes v.e0 ++ Arm.beBytes v.e1 ++ Arm.beBytes v.e2 ++ Arm.beBytes v.e3).map (⟨·⟩)

/-- [slhdsa::sha256::hw::arm::store_be]: `vrev32q_u8` then `vst1q_u8` at
`b[at..at + 16]`, after `assert!(b.len() >= 16 && at <= b.len() - 16)`. -/
def sha256.hw.arm.store_be (b : Slice Std.U8) (at' : Std.Usize)
  (v : core.core_arch.arm_shared.neon.uint32x4_t) : Result (Slice Std.U8) :=
  if Arm.haveSha2 then
    if 16 ≤ b.length ∧ at'.val ≤ b.length - 16 then
      ok (b.setSlice! at'.val (sha256.hw.arm.be_bytes v))
    else fail .panic
  else fail .undef

/-- [slhdsa::sha256::hw::arm::add]: `vaddq_u32`. -/
def sha256.hw.arm.add (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.ADD a b) else fail .undef

/-- [slhdsa::sha256::hw::arm::or]: `vorrq_u32`. -/
def sha256.hw.arm.or (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.ORR a b) else fail .undef

/-- [slhdsa::sha256::hw::arm::and]: `vandq_u32`. -/
def sha256.hw.arm.and (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.AND a b) else fail .undef

/-- [slhdsa::sha256::hw::arm::shr16]: `vshrq_n_u32(a, 16)`. -/
def sha256.hw.arm.shr16 (a : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.USHR a 16) else fail .undef

/-- [slhdsa::sha256::hw::arm::shl16]: `vshlq_n_u32(a, 16)`. -/
def sha256.hw.arm.shl16 (a : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.SHL a 16) else fail .undef

/-- [slhdsa::sha256::hw::arm::ext2]: `vextq_u32(a, b, 2)`. -/
def sha256.hw.arm.ext2 (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.EXT2 a b) else fail .undef

/-- [slhdsa::sha256::hw::arm::ext3]: `vextq_u32(a, b, 3)`. -/
def sha256.hw.arm.ext3 (a b : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.EXT3 a b) else fail .undef

/-- [slhdsa::sha256::hw::arm::sha256h]: `vsha256hq_u32(hash_abcd, hash_efgh, wk)`,
the instruction `SHA256H` with `Qd = hash_abcd`, `Qn = hash_efgh`, `Vm = wk`. -/
def sha256.hw.arm.sha256h (abcd efgh wk : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.SHA256H abcd efgh wk) else fail .undef

/-- [slhdsa::sha256::hw::arm::sha256h2]: `vsha256h2q_u32(hash_efgh, hash_abcd, wk)`,
the instruction `SHA256H2` with `Qd = hash_efgh`, `Qn = hash_abcd`, `Vm = wk`. -/
def sha256.hw.arm.sha256h2 (efgh abcd wk : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.SHA256H2 efgh abcd wk) else fail .undef

/-- [slhdsa::sha256::hw::arm::sha256su0]: `vsha256su0q_u32(w0_3, w4_7)`, the
instruction `SHA256SU0` with `Vd = w0_3`, `Vn = w4_7`. -/
def sha256.hw.arm.sha256su0 (w0_3 w4_7 : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.SHA256SU0 w0_3 w4_7) else fail .undef

/-- [slhdsa::sha256::hw::arm::sha256su1]: `vsha256su1q_u32(tw0_3, w8_11, w12_15)`,
the instruction `SHA256SU1` with `Vd = tw0_3`, `Vn = w8_11`, `Vm = w12_15`. -/
def sha256.hw.arm.sha256su1 (tw0_3 w8_11 w12_15 : core.core_arch.arm_shared.neon.uint32x4_t) :
  Result core.core_arch.arm_shared.neon.uint32x4_t :=
  if Arm.haveSha2 then ok (Arm.SHA256SU1 tw0_3 w8_11 w12_15) else fail .undef

end slhdsa
