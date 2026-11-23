module
public import Kmixed.Types
public import Ksha3.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace KmixedRust.core.core_arch
open arm_shared.neon
namespace arm_shared.neon.generated
abbrev veorq_u64 := Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64
abbrev vdupq_n_u64 := Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64
def vbicq_u64 (a b : uint64x2_t) : Result uint64x2_t := ok fun j => a j &&& ~~~(b j)
def vshlq_n_u64 (n : I32) (x : uint64x2_t) : Result uint64x2_t := ok fun j => x j <<< n.bv.toNat
end arm_shared.neon.generated
def aarch64.neon.generated.vsriq_n_u64 (n : I32) (a b : uint64x2_t) : Result uint64x2_t :=
  ok fun j => ((a j) &&& (BitVec.allOnes 64 <<< (64-n.bv.toNat))) ||| ((b j) >>> n.bv.toNat)
end KmixedRust.core.core_arch
