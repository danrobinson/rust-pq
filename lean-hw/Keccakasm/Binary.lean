import Keccakasm.Proof

/-! Restricted semantics and encodings for the linked System V AVX-512 Keccak leaf.
All data operations act independently on each of the eight 64-bit vector lanes.
Register 32 models that lane's word in the single 64-byte red-zone spill.
The address forms and the control skeleton are fixed by the encodings below. -/
namespace slhdsa.KeccakAsm.Binary
open Spec.Keccak

abbrev Reg := Fin 32
abbrev Registers := Nat → Lane
inductive Source where
  | reg (r : Reg)
  | spill
  | rc
  deriving Repr

inductive Op where
  | mov (dst src : Reg)
  | spill (src : Reg)
  | xor (dst lhs : Reg) (rhs : Source)
  | tern (dst lhs rhs : Reg) (imm : UInt8)
  | rol (dst src : Reg) (shift : UInt8)
  deriving Repr

def write (s : Registers) (i : Nat) (v : Lane) : Registers := fun j => if j = i then v else s j

def execute (rc : Lane) (s : Registers) : Op → Registers
  | .mov d r => write s d (s r)
  | .spill r => write s 32 (s r)
  | .xor d l r => write s d (s l ^^^ (match r with
      | .reg i => s i | .spill => s 32 | .rc => rc))
  | .tern d l r i => write s d (X86.ternary i.toNat (s d) (s l) (s r))
  | .rol d r i => write s d ((s r).rotateLeft i.toNat)

abbrev Bytes := List UInt8

private def invBit (n bit weight : Nat) := if n.testBit bit then 0 else weight

/-- Four-byte EVEX prefix, followed by the opcode and ModR/M byte.
W=1, L'L=10 (512-bit vectors), aaa=0 (unmasked), z=0. -/
private def evex (map pp opcode reg v rm mode : Nat) (broadcast : Bool := false) : Bytes :=
  [0x62, (invBit reg 3 128 + invBit rm 4 64 + invBit rm 3 32 + invBit reg 4 16 + map).toUInt8,
   (128 + (15 - v % 16)*8 + 4 + pp).toUInt8,
   (64 + (if broadcast then 16 else 0) + invBit v 4 8).toUInt8,
   opcode.toUInt8, (mode*64 + reg%8*8 + rm%8).toUInt8]

/-- State row i starts at rdi + 64*i; EVEX disp8 is scaled by the 64-byte tuple. -/
def rowMove (store : Bool) (r : Reg) (i : Nat) : Bytes :=
  evex 1 2 (if store then 0x7f else 0x6f) r 0 7 (if i=0 then 0 else 1) ++
  (if i=0 then [] else [i.toUInt8])

/-- SIB for [rsp-72], followed by the sign-extended 32-bit displacement. -/
private def redZone : Bytes := [0x24,0xb8,0xff,0xff,0xff]

def encode : Op → Bytes
  | .mov d r => evex 1 1 0x6f d 0 r 3
  | .spill r => evex 1 2 0x7f r 0 4 2 ++ redZone
  | .xor d l (.reg r) => evex 1 1 0xef d l r 3
  | .xor d l .spill => evex 1 1 0xef d l 4 2 ++ redZone
  | .xor d l .rc => evex 1 1 0xef d l 4 0 true ++ [0x01] -- [rcx+rax]{1to8}
  | .tern d l r i => evex 3 1 0x25 d l r 3 ++ [i]
  | .rol d r i => evex 1 1 0x72 1 d r 3 ++ [i]

def littleEndian (n count : Nat) : Bytes := (List.range count).map fun i => (n >>> (8*i)).toUInt8

private def rel32 (target next : Nat) : Bytes :=
  littleEndian (((target : Int) - next) % 2^32).toNat 4

/-- Complete leaf from the first load through RET. Both RIP-relative displacements
are computed from actual virtual addresses. The only conditional jump returns to the
first round instruction. The 32-bit XOR clears all of RCX; the 64-bit loop increments
it by 8 until it reaches 192. -/
def imageCode (rows : List Reg) (ops : List Op) (entry table : Nat) : Bytes := Id.run do
  let loads := rows.zipIdx.flatMap fun (r,i) => rowMove false r i
  let stores := rows.zipIdx.flatMap fun (r,i) => rowMove true r i
  let leaEnd := entry + loads.length + 2 + 7
  let alignment : Bytes := [0x66,0x0f,0x1f,0x84,0,0,0,0,0]
  let loopStart := leaEnd + alignment.length
  let body := ops.flatMap encode
  let tail : Bytes := [0x48,0x83,0xc1,0x08,0x48,0x81,0xf9,0xc0,0,0,0,0x0f,0x85]
  let jumpEnd := loopStart + body.length + tail.length + 4
  return loads ++ [0x31,0xc9,0x48,0x8d,0x05] ++ rel32 table leaEnd ++ alignment ++
    body ++ tail ++ rel32 loopStart jumpEnd ++ stores ++ [0xc5,0xf8,0x77,0xc3]

end slhdsa.KeccakAsm.Binary
