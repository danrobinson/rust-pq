import Spec.Sha256

namespace Spec.Keccak

abbrev Lane := BitVec 64
abbrev State := Array Lane

/-- FIPS 202 Table 2 in row order x + 5y. -/
def rotations : Array Nat := #[0,1,62,28,27, 36,44,6,55,20, 3,10,43,25,39,
  41,45,15,21,8, 18,2,61,56,14]

/-- FIPS 202 Algorithm 5, evaluated for the 24 rounds of Keccak-f[1600]. -/
def rc : Array Lane := #[
  0x0000000000000001,0x0000000000008082,0x800000000000808a,0x8000000080008000,
  0x000000000000808b,0x0000000080000001,0x8000000080008081,0x8000000000008009,
  0x000000000000008a,0x0000000000000088,0x0000000080008009,0x000000008000000a,
  0x000000008000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,
  0x8000000000008002,0x8000000000000080,0x000000000000800a,0x800000008000000a,
  0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008]

def parity (a : State) (x : Nat) : Lane :=
  a[x]! ^^^ a[x+5]! ^^^ a[x+10]! ^^^ a[x+15]! ^^^ a[x+20]!

def delta (a : State) (x : Nat) : Lane :=
  parity a ((x+4)%5) ^^^ (parity a ((x+1)%5)).rotateLeft 1

def theta (a : State) (i : Nat) : Lane := a[i]! ^^^ delta a (i%5)

def rhoPi (a : State) (i : Nat) : Lane :=
  let x := i%5
  let y := i/5
  let src := (x + 3*y)%5 + 5*x
  (theta a src).rotateLeft rotations[src]!

def chi (b : State) (i : Nat) : Lane :=
  let row := i/5*5
  b[i]! ^^^ ((~~~b[row+(i+1)%5]!) &&& b[row+(i+2)%5]!)

def round (a : State) (constant : Lane) : State := Id.run do
  let b := Array.ofFn (n := 25) fun i => rhoPi a i.val
  return Array.ofFn (n := 25) fun i =>
    if i.val = 0 then chi b i.val ^^^ constant else chi b i.val

def permute (a : State) : State := rc.foldl round a

/-- XOR byte b into its little-endian lane at a rate position. -/
def xorByte (a : State) (pos : Nat) (b : Byte) : State :=
  a.setIfInBounds (pos/8) (a[pos/8]! ^^^ (b.zeroExtend 64 <<< (8*(pos%8))))

/-- Absorb one byte, permuting after each complete 1088-bit rate block. -/
def feed (s : State × Nat) (b : Byte) : State × Nat :=
  let lanes := xorByte s.1 s.2 b
  if s.2+1 = 136 then (permute lanes, 0) else (lanes, s.2+1)

def initial : State × Nat := (Array.replicate 25 0, 0)

/-- The SHAKE domain bits and the first padding bit form 0x1f. The last
padding bit occupies the high bit of byte 135, including when both coincide. -/
def finalize (s : State × Nat) : State :=
  permute (xorByte (xorByte s.1 s.2 0x1f) 135 0x80)

/-- Extract the next byte from the rate, applying the permutation whenever
another output block is needed. -/
def extractByte (a : State) (pos : Nat) : Byte :=
  (a[pos/8]! >>> (8*(pos%8))).truncate 8

def squeeze (a : State) (pos : Nat) : Nat → Bytes
  | 0 => []
  | n+1 =>
    let (block, atPos) := if pos = 136 then (permute a, 0) else (a, pos)
    extractByte block atPos :: squeeze block (atPos+1) n

end Spec.Keccak

/-- FIPS 202 SHAKE256 on byte strings, with the requested length in bytes. -/
def Spec.shake256 (m : Bytes) (length : Nat) : Bytes :=
  let a := Keccak.finalize (m.foldl Keccak.feed Keccak.initial)
  Keccak.squeeze a 0 length

namespace Spec

@[simp] theorem Keccak.squeeze_length (a : State) (pos n : Nat) :
    (squeeze a pos n).length = n := by
  induction n generalizing a pos with
  | zero => rfl
  | succ n ih => simp [squeeze, ih]

@[simp] theorem shake256_length (m : Bytes) (n : Nat) : (shake256 m n).length = n := by
  simp [shake256]

end Spec
