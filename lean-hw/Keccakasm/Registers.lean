module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result
namespace slhdsa.KeccakRegisters
abbrev Matrix (width : Usize) := Array (Array U64 width) 25#usize
abbrev Regs (width : Usize) := Array (Fin width.val → BitVec 64) 25#usize

/-- Little-endian native word lanes preserve both row and lane order under transmute. -/
def pack {width} (x : Matrix width) : Regs width :=
  Array.from (x.val.map fun row j => row.val[j.val]!.bv) (by simp)
def unpack {width} (x : Regs width) : Matrix width :=
  Array.from (x.val.map fun row =>
    Array.from (List.ofFn (fun j : Fin width.val => (⟨row j⟩ : U64))) (by simp)) (by simp)

class Cast (Source Target : Type) where
  bits : Source → Target
instance {width} : Cast (Matrix width) (Regs width) := ⟨pack⟩
instance {width} : Cast (Regs width) (Matrix width) := ⟨unpack⟩
def transmute {Source : Type} (Target : Type) [Cast Source Target] (x : Source) : Result Target :=
  ok (Cast.bits x)
end slhdsa.KeccakRegisters
