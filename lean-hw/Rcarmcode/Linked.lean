import Rcarmcode.Proof
import Rcarmcode.Proof512

namespace slhdsa.RcArmCode.Linked

/-- AArch64 vector ADD with Q=1,size=11. The result describes the one
    destination update. This instruction preserves flags and all other registers. -/
def vectorAdd (word : Nat) (regs : Nat → Arm.V2) : Option (Nat × Arm.V2) :=
  if word &&& 0xffe0fc00 == 0x4ee08400 then
    some (word % 32, Arm.ADD2 (regs ((word / 32) % 32)) (regs ((word / 65536) % 32)))
  else none

/-- The linked SHA-512 compressor interchanges Rn and Rm for this single ADD. -/
theorem linked_add_equivalent (regs : Nat → Arm.V2) :
    vectorAdd 0x4ef98463 regs = vectorAdd 0x4ee38723 regs := by
  change some (3, Arm.ADD2 (regs 3) (regs 25)) = some (3, Arm.ADD2 (regs 25) (regs 3))
  simp [Arm.ADD2, BitVec.add_comm]

end slhdsa.RcArmCode.Linked
