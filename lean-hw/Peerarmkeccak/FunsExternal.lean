module
public import Peerarmkeccak.Types
public import Ksha3.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace PeerArmRust
abbrev core.core_arch.aarch64.neon.generated.vbcaxq_u64 := Ksha3Rust.core.core_arch.aarch64.neon.generated.vbcaxq_u64
abbrev core.core_arch.aarch64.neon.generated.veor3q_u64 := Ksha3Rust.core.core_arch.aarch64.neon.generated.veor3q_u64
abbrev core.core_arch.aarch64.neon.generated.vrax1q_u64 := Ksha3Rust.core.core_arch.aarch64.neon.generated.vrax1q_u64
abbrev core.core_arch.aarch64.neon.generated.vxarq_u64 := Ksha3Rust.core.core_arch.aarch64.neon.generated.vxarq_u64
abbrev core.core_arch.arm_shared.neon.generated.vdupq_n_u64 := Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64
abbrev core.core_arch.arm_shared.neon.generated.veorq_u64 := Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64

def core.core_arch.arm_shared.neon.generated.vcreate_u64 (a : U64) : Result (BitVec 64) := ok a.bv
def core.core_arch.arm_shared.neon.generated.vcombine_u64 (a b : BitVec 64) :
    Result core.core_arch.arm_shared.neon.uint64x2_t := ok fun i => if i.val=0 then a else b
def core.core_arch.arm_shared.neon.generated.vgetq_lane_u64 (i : I32) (a : core.core_arch.arm_shared.neon.uint64x2_t) : Result U64 :=
  if h : i.bv.toNat<2 then ok ⟨a ⟨i.bv.toNat,h⟩⟩ else fail .panic
end PeerArmRust
