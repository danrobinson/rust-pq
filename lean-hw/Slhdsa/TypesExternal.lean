-- [slhdsa]: external types.
-- Hand-written: the meaning of the types Aeneas does not translate.
module
public import Aeneas
public import Arm
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [core::core_arch::arm_shared::neon::uint32x4_t]: a 128-bit register as
four 32-bit elements. -/
@[rust_type "core::core_arch::arm_shared::neon::uint32x4_t"]
def core.core_arch.arm_shared.neon.uint32x4_t : Type := Arm.V

/-- [core::core_arch::arm_shared::neon::uint64x2_t]: a 128-bit register as
two 64-bit elements. -/
@[rust_type "core::core_arch::arm_shared::neon::uint64x2_t"]
def core.core_arch.arm_shared.neon.uint64x2_t : Type := Arm.V2
