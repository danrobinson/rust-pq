module
public import Ksha3.Types

@[expose] public section
open Aeneas Aeneas.Std Result
namespace Ksha3Rust
def core.core_arch.aarch64.neon.generated.vbcaxq_u64 (a : core.core_arch.arm_shared.neon.uint64x2_t) (b : core.core_arch.arm_shared.neon.uint64x2_t) (c : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint64x2_t := ok (fun j => a j ^^^ (b j &&& ~~~(c j)))
def core.core_arch.aarch64.neon.generated.veor3q_u64 (a : core.core_arch.arm_shared.neon.uint64x2_t) (b : core.core_arch.arm_shared.neon.uint64x2_t) (c : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint64x2_t := ok (fun j => a j ^^^ b j ^^^ c j)
def core.core_arch.aarch64.neon.generated.vrax1q_u64 (a : core.core_arch.arm_shared.neon.uint64x2_t) (b : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint64x2_t := ok (fun j => a j ^^^ (b j).rotateLeft 1)
def core.core_arch.aarch64.neon.generated.vxarq_u64 (imm : I32) (a : core.core_arch.arm_shared.neon.uint64x2_t) (b : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint64x2_t := ok (fun j => (a j ^^^ b j).rotateRight (imm.bv.toNat%64))
def core.core_arch.arm_shared.neon.generated.vdupq_n_u64 (unsigned : U64) : Result core.core_arch.arm_shared.neon.uint64x2_t := ok (fun _ => unsigned.bv)
def core.core_arch.arm_shared.neon.generated.veorq_u64 (a : core.core_arch.arm_shared.neon.uint64x2_t) (b : core.core_arch.arm_shared.neon.uint64x2_t) : Result core.core_arch.arm_shared.neon.uint64x2_t := ok (fun j => a j ^^^ b j)
end Ksha3Rust
