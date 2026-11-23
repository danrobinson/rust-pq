import Spec.Shake256

/-! A lane of the arm64 SHA3 register machine. The two 64-bit lanes of the
supported vector operations execute independently. The caller supplies the
constant loaded from memory. Scalar counter/address updates preserve SIMD state. -/
namespace Spec.ArmSha3Binary
open Spec.Keccak

abbrev Registers := Nat → Lane

def step (rc : Lane) (r : Registers) (w : Nat) : Option Registers := do
  let d := w % 32
  let n := w / 32 % 32
  let m := w / 65536 % 32
  let a := w / 1024 % 32
  if w == 0x8b08012a || w == 0x91002108 then return r
  let v ←
    if w &&& 0xffe08000 == 0xce000000 then some (r n ^^^ r m ^^^ r a)
    else if w &&& 0xffe08000 == 0xce200000 then some (r n ^^^ ((~~~r a) &&& r m))
    else if w &&& 0xffe0fc00 == 0xce608c00 then some (r n ^^^ (r m).rotateLeft 1)
    else if w &&& 0xffe00000 == 0xce800000 then
      some ((r n ^^^ r m).rotateLeft ((64 - w / 1024 % 64) % 64))
    else if w &&& 0xffe0fc00 == 0x4ea01c00 && n == m then some (r n)
    else if w &&& 0xffe0fc00 == 0x6e201c00 then some (r n ^^^ r m)
    else if w == 0x4d40cd40 then some rc
    else none
  return fun j => if j == d then v else r j

def run (code layout : List Nat) (a : State) (rc : Lane) (scratch : Registers) :
    Option State := do
  let initial := (layout.zipIdx).foldl (fun r (reg, row) j =>
    if j == reg then a[row]! else r j) scratch
  let result ← code.foldlM (step rc) initial
  return (layout.map result).toArray
/-- The inlined rate-block round uses one 16-byte spill at SP. Register 32 models
the corresponding 64-bit half of the spill. The round checker validates the effective
constant address and counter increments against the enclosing loop. -/
def stepBulk (rc : Lane) (r : Registers) (w : Nat) : Option Registers :=
  if w == 0x8b0a012b || w == 0x9100214a then some r
  else if w == 0x3d8003e5 then some (fun j => if j == 32 then r 5 else r j)
  else if w == 0x3dc003e4 then some (fun j => if j == 4 then r 32 else r j)
  else if w == 0x4d40cd60 then some (fun j => if j == 0 then rc else r j)
  else step rc r w

def runBulk (code layout : List Nat) (a : State) (rc : Lane) (scratch : Registers) :
    Option State := do
  let initial := (layout.zipIdx).foldl (fun r (reg, row) j =>
    if j == reg then a[row]! else r j) scratch
  let result ← code.foldlM (stepBulk rc) initial
  return (layout.map result).toArray

/-- The linked UMULH/LSR sequence for the count of whole 136-byte rate blocks. -/
theorem rateQuotient (n : Nat) (h : n < 2^64) :
    n * 0xf0f0f0f0f0f0f0f1 / 2^64 / 128 = n / 136 := by omega

end Spec.ArmSha3Binary
