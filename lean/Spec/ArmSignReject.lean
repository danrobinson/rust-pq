import Std

/-! A partial AArch64 symbolic executor for linked Rust signing entries. Words are symbolic
64-bit values. Stack, key and indirect result are disjoint live regions. A symbolic initial
register or input word stands for any value; storing and loading it preserves that value.
The decoder refuses every instruction and effective address outside the modeled subset.
The observed path must start at the supplied symbol and end with RET to its incoming LR. -/
namespace Spec.ArmSignReject

inductive Word where
  | reg (i : Nat) | vec (i lane : Nat) | keyWord (offset : Nat)
  | frame (offset : Int) | key | result | lit (value : Nat)
deriving DecidableEq, Repr

structure State where
  pc : Word
  g : Nat → Word := .reg
  q : Nat → Nat → Word := .vec
  sp : Int := 0
  stack : List (Int × Word) := []
  output : List Word := []
  keyReads : List Nat := []
  /-- Unsigned LS flag after comparing the incoming length against a literal. -/
  ls : Option Bool := none

def initial (entry : Nat) : State := {
  pc := .lit entry
  g := fun i => if i == 4 then .key else if i == 8 then .result else .reg i
}

def readReg (s : State) (i : Nat) := if i == 31 then Word.frame s.sp else s.g i

def putReg (s : State) (i : Nat) (v : Word) : Option State := do
  if i == 31 then
    let .frame n := v | none
    guard (n ≤ 0 && -160 ≤ n && n % 16 == 0)
    return { s with sp := n }
  return {s with g := fun j => if i == j then v else s.g j}

def offset : Word → Int → Option Word
  | .frame p, d => some (.frame (p+d))
  | .lit p, d => some (.lit ((p+d) % (2^64 : Int)).toNat)
  | _, _ => none

def inFrame (s : State) (addr : Int) := s.sp ≤ addr && addr + 8 ≤ 0 && addr % 8 == 0

def load (s : State) (base : Word) (off : Nat) : Option (Word × State) := do
  match base with
  | .frame p =>
    guard (inFrame s (p+off))
    let v ← s.stack.lookup (p+off)
    return (v,s)
  | .key => return (.keyWord off, {s with keyReads := off :: s.keyReads})
  | _ => none

def store (s : State) (base : Word) (off : Nat) (v : Word) : Option State := do
  match base with
  | .frame p =>
    guard (inFrame s (p+off))
    return {s with stack := (p+off,v) :: s.stack}
  | .result =>
    guard (off == 0)
    return {s with output := v :: s.output}
  | _ => none

/-- Little-endian 64-bit lanes. A scalar store uses XZR for register 31.
The observed path needs neither a zero-register transfer nor a signed pair offset. -/
def transfer (s : State) (ld simd : Bool) (r : Nat) (base : Word) (off : Nat) : Option State := do
  guard (r < 31)
  if ld then
    let (lo,s) ← load s base off
    if simd then
      let (hi,s) ← load s base (off+8)
      return {s with q := fun j l => if j == r then (if l == 0 then lo else hi) else s.q j l}
    putReg s r lo
  else if simd then
    let s ← store s base off (s.q r 0)
    store s base (off+8) (s.q r 1)
  else store s base off (s.g r)

def signed (v bits : Nat) : Int :=
  if v < 2^(bits-1) then v else (v : Int) - 2^bits

def branchDest (pc : Nat) (delta : Int) := Word.lit (((pc : Int)+4*delta) % (2^64 : Int)).toNat

/-- On any 64-bit context length in the stated range, CMP length,255 followed by
B.LS falls through. This also covers values with the top bit set. -/
theorem unsigned_long (length : BitVec 64) (h : 255 < length.toNat) :
    decide (length.toNat ≤ 255) = false := by simp [Nat.not_le.mpr h]

def step (contextLS : Bool) (op : Nat × Nat) (s : State) : Option State := do
  let (pc,w) := op
  guard (s.pc == .lit pc && pc % 4 == 0 && w < 2^32)
  let s := {s with pc := .lit (pc+4)}
  let d := w % 32
  let n := (w >>> 5) % 32
  let m := (w >>> 16) % 32
  let imm := (w >>> 10) % 4096
  let mask := fun k => w &&& k
  if mask 0xffe0ffe0 == 0xaa0003e0 then
    guard (d < 31 && m < 31)
    putReg s d (s.g m)
  else if mask 0xffc00000 == 0x91000000 || mask 0xffc00000 == 0xd1000000 then
    let delta : Int := if mask 0xffc00000 == 0x91000000 then imm else -(imm : Int)
    putReg s d (← offset (readReg s n) delta)
  else if mask 0x9f000000 == 0x90000000 then
    guard (d < 31)
    let pages := signed (((w >>> 5) % 2^19)*4 + ((w >>> 29) % 4)) 21
    putReg s d (.lit (((pc / 4096 * 4096 : Nat) + pages*4096 : Int) % (2^64 : Int)).toNat)
  else if mask 0xffe00000 == 0x52800000 then
    guard (d < 31)
    putReg s d (.lit ((w >>> 5) % 65536))
  else if mask 0xffffffe0 == 0x92800000 then
    guard (d < 31)
    putReg s d (.lit (2^64-1))
  else if mask 0xffc0001f == 0xf100001f then
    guard (s.g n == .reg 3 && imm == 255)
    return {s with ls := some contextLS}
  else if mask 0xff00001f == 0x54000009 then
    let ls ← s.ls
    return {s with pc := if ls then branchDest pc (signed ((w >>> 5) % 2^19) 19) else .lit (pc+4)}
  else if mask 0x7c000000 == 0x14000000 then
    let dest := branchDest pc (signed (w % 2^26) 26)
    let s ← if w >>> 31 == 1 then putReg s 30 (.lit (pc+4)) else some s
    return {s with pc := dest}
  else if w == 0xd65f03c0 then return {s with pc := s.g 30}
  else
    let kind := mask 0xffc00000
    let ld := (w >>> 22) % 2 == 1
    let base := readReg s n
    if [0xf9400000,0xf9000000,0x3dc00000,0x3d800000].contains kind then
      let simd := w >>> 30 == 0
      transfer s ld simd d base (imm * (if simd then 16 else 8))
    else if [0xa9400000,0xa9000000,0xad400000,0xad000000].contains kind then
      let simd := (w >>> 26) % 2 == 1
      let size := if simd then 16 else 8
      let u := (w >>> 15) % 128
      guard (u < 64)
      let s ← transfer s ld simd d base (u*size)
      transfer s ld simd ((w >>> 10) % 32) base ((u+1)*size)
    else none

/-- Check the complete path under all substitutions of the independent symbolic inputs.
Output is an exact log of stores to the caller's result; other non-frame stores are rejected.
The only accepted reads outside the current stack allocation are exactly the listed key words. -/
def post (width : Nat) (det : Bool) (s : State) : Bool :=
  s.pc == .reg 30 && s.sp == 0 && s.ls == some false &&
    s.output == [.lit (2^64-1)] &&
    s.keyReads.reverse == (if det then (List.range (width/8)).map (fun j => 2*width+8*j) else []) &&
    (List.range 13).all (fun j => s.g (18+j) == .reg (18+j)) &&
    (List.range 8).all (fun j => (List.range 2).all (fun lane => s.q (8+j) lane == .vec (8+j) lane))

def run (contextLS : Bool) (entry : Nat) (path : List (Nat × Nat)) : Option State :=
  path.foldlM (fun s op => step contextLS op s) (initial entry)

def checks (entry width : Nat) (det : Bool) (path : List (Nat × Nat)) : Bool :=
  match run false entry path with
  | some s => post width det s
  | none => false

/-- The concrete instruction sequence executes to the caller's continuation for every long
context, with the exact output write, ABI-preserved registers and key footprint in `post`. -/
def ReturnsNone (entry width : Nat) (det : Bool) (path : List (Nat × Nat)) : Prop :=
  ∀ length : BitVec 64, 255 < length.toNat →
    ∃ s, run (decide (length.toNat ≤ 255)) entry path = some s ∧ post width det s = true

theorem returnsNone_of_checks {entry width det path} (check : checks entry width det path = true) :
    ReturnsNone entry width det path := by
  intro length h
  rw [unsigned_long length h]
  unfold checks at check
  cases hr : run false entry path with
  | none => simp [hr] at check
  | some s => exact ⟨s, rfl, by simpa [hr] using check⟩

end Spec.ArmSignReject
