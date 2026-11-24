module
public import Rcni.Types
public import Shani.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RcNiRust.Memory
open slhdsa.Intel

/-- Little-endian 16-byte unaligned load followed by PSHUFB. The caller supplies
the two 64-bit mask operands in Intel intrinsic order and a register offset. -/
def shuffled (b : Array U8 64#usize) (hi lo : BitVec 64) (index : Nat) : Reg :=
  let bytes := b.val.map U8.bv
  let mask := hi ++ lo
  let byte (i : Nat) : BitVec 8 :=
    let selector := mask.extractLsb' (8*i) 8
    if selector.msb then 0 else bytes[16*index + selector.toNat % 16]!
  let word (i : Nat) : Word := byte (i+3) ++ byte (i+2) ++ byte (i+1) ++ byte i
  ⟨word 0,word 4,word 8,word 12⟩

def readState (s : Array U32 8#usize) (index : Nat) : Reg :=
  let get (k : Nat) := s.val[4*index+k]!.bv
  ⟨get 0,get 1,get 2,get 3⟩

/-- Store one unaligned XMM register at a register-scaled displacement in
an exclusive eight-word state. Each store preserves the other half. -/
def store (s : Array U32 8#usize) (index : Fin 2) (v : Reg) : Array U32 8#usize :=
  let old := readState s (1-index.val)
  let (a,b) := if index.val=0 then (v,old) else (old,v)
  Array.make 8#usize [⟨a.w0⟩,⟨a.w1⟩,⟨a.w2⟩,⟨a.w3⟩,⟨b.w0⟩,⟨b.w1⟩,⟨b.w2⟩,⟨b.w3⟩]
end RcNiRust.Memory
