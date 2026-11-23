/-! Straight-line AArch64 word semantics for the instructions that compare
    the recovered hypertree root to the root in the public key. Reads use a
    memory of little-endian 64-bit loads; all referenced addresses must be readable. -/
namespace LinkedArm.RootComparison

abbrev Word := BitVec 64
abbrev Memory := Word → Word
structure State where
  regs : Nat → Word
  sp : Word
  z : Bool

def base (s : State) (i : Nat) := if i == 31 then s.sp else s.regs i

def operand (s : State) (i : Nat) := if i == 31 then 0 else s.regs i

def write (s : State) (i : Nat) (v : Word) : State :=
  if i == 31 then s else { s with regs := fun j => if i == j then v else s.regs j }

/-- Unknown words and unsupported addressing/condition modes fail closed. -/
def step (mem : Memory) (s : State) (w : Nat) : Option State := do
  let rd := w % 32
  let rn := (w / 32) % 32
  let rm := (w / 65536) % 32
  if w &&& 0xffc00000 == 0xa9400000 then
    let imm := (w / 32768) % 128
    let disp := BitVec.signExtend 64 (BitVec.ofNat 7 imm)
    let addr := base s rn + disp * 8
    let rt2 := (w / 1024) % 32
    if rt2 == rd then none
    else return write (write s rd (mem addr)) rt2 (mem (addr + 8))
  else if w &&& 0xffc00000 == 0xf9400000 then
    return write s rd (mem (base s rn + BitVec.ofNat 64 (8 * ((w / 1024) % 4096))))
  else if w &&& 0xffe0fc1f == 0xeb00001f then
    return { s with z := operand s rn == operand s rm }
  else if w &&& 0xffe0fc1f == 0xfa400000 then
    return { s with z := s.z && (operand s rn == operand s rm) }
  else if w == 0x1a9f17e0 then
    return write s 0 (if s.z then 1 else 0)
  else none

def verdict (ops : List Nat) (mem : Memory) (s : State) : Option Word := do
  let final ← ops.foldlM (step mem) s
  return final.regs 0

def root (mem : Memory) (addr : Word) (lanes : Nat) :=
  (List.range lanes).map fun i => mem (addr + BitVec.ofNat 64 (8*i))

end LinkedArm.RootComparison
