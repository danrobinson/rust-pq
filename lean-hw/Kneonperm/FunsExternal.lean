module
public import Kneonperm.Types
public import Kneon.Funs
public import Keccakasm.Registers
@[expose] public section
namespace KneonpermRust
open Aeneas Aeneas.Std slhdsa.KeccakRegisters
instance : Cast (Matrix 2#usize) (Array KneonRust.core.core_arch.arm_shared.neon.uint64x2_t 25#usize) :=
  ⟨pack (width := 2#usize)⟩
instance : Cast (Array KneonRust.core.core_arch.arm_shared.neon.uint64x2_t 25#usize) (Matrix 2#usize) :=
  ⟨unpack (width := 2#usize)⟩
abbrev core.intrinsics.transmute {Source : Type} (Target : Type) [slhdsa.KeccakRegisters.Cast Source Target] := @slhdsa.KeccakRegisters.transmute Source Target _
abbrev shake256.parallel.neon.round := KneonRust.shake256.parallel.neon.round
end KneonpermRust
