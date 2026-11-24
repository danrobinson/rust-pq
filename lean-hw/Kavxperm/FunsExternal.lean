module
public import Kavxperm.Types
public import Kavx.Funs
public import Keccakasm.Registers
@[expose] public section
namespace KavxpermRust
open Aeneas Aeneas.Std slhdsa.KeccakRegisters
instance : Cast (Matrix 8#usize) (Array KavxRust.core.core_arch.x86.__m512i 25#usize) :=
  ⟨pack (width := 8#usize)⟩
instance : Cast (Array KavxRust.core.core_arch.x86.__m512i 25#usize) (Matrix 8#usize) :=
  ⟨unpack (width := 8#usize)⟩
abbrev core.intrinsics.transmute {Source : Type} (Target : Type) [slhdsa.KeccakRegisters.Cast Source Target] := @slhdsa.KeccakRegisters.transmute Source Target _
abbrev shake256.parallel.avx512.round := KavxRust.shake256.parallel.avx512.round
end KavxpermRust
