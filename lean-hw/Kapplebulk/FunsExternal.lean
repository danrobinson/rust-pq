module
public import Kapplebulk.Types
public import Parent512.FunsExternal
public import Ksha3.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace KapplebulkRust
abbrev shake256.parallel.sha3.round := Ksha3Rust.shake256.parallel.sha3.round
namespace core.core_arch.arm_shared.neon.generated
abbrev vdupq_n_u64 := Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64
abbrev veorq_u64 := Ksha3Rust.core.core_arch.arm_shared.neon.generated.veorq_u64
def vgetq_lane_u64 (idx : I32) (v : uint64x2_t) : Result U64 :=
  if h : idx.bv.toNat < 2 then ok ⟨v ⟨idx.bv.toNat,h⟩⟩ else fail .undef
end core.core_arch.arm_shared.neon.generated
end KapplebulkRust
