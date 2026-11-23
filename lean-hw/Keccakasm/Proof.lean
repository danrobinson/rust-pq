import Keccakasm.Code
import Spec.ShakeWords
import Mathlib.Tactic.IntervalCases
open Spec.Keccak
namespace slhdsa.KeccakAsm

theorem chiInstruction (a b c : Lane) : X86.ternary 210 a b c = a ^^^ ((~~~b) &&& c) := by
  change X86.selectWord a (X86.selectWord b (X86.selectWord c (BitVec.allOnes 64) (BitVec.allOnes 64))
    (X86.selectWord c 0#64 (BitVec.allOnes 64))) (X86.selectWord b (X86.selectWord c 0#64 0#64)
    (X86.selectWord c (BitVec.allOnes 64) 0#64)) = _
  ext i hi
  simp only [X86.selectWord,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,BitVec.getElem_xor,
    BitVec.getElem_zero,BitVec.getElem_allOnes]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

set_option maxRecDepth 65536
set_option maxHeartbeats 800000
private theorem rotzero (x : Lane) : x.rotateLeft 0 = x := by
  simp [BitVec.rotateLeft_def, BitVec.ushiftRight_eq_zero]

private theorem cell0 (a : State) (rc : Lane) : word0 a rc = (round a rc)[0]! := by
  rw [roundAt _ _ _ (by decide)]
  change word0 a rc = ((a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 0 ^^^ ((~~~(a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 44) &&& (a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 43)) ^^^ rc
  simp only [word0, chiInstruction, X86.xor3, rotzero]
  ac_rfl

private theorem cell1 (a : State) (rc : Lane) : word1 a rc = (round a rc)[1]! := by
  rw [roundAt _ _ _ (by decide)]
  change word1 a rc = ((a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 44 ^^^ ((~~~(a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 43) &&& (a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 21))
  simp only [word1, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell2 (a : State) (rc : Lane) : word2 a rc = (round a rc)[2]! := by
  rw [roundAt _ _ _ (by decide)]
  change word2 a rc = ((a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 43 ^^^ ((~~~(a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 21) &&& (a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 14))
  simp only [word2, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell3 (a : State) (rc : Lane) : word3 a rc = (round a rc)[3]! := by
  rw [roundAt _ _ _ (by decide)]
  change word3 a rc = ((a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 21 ^^^ ((~~~(a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 14) &&& (a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 0))
  simp only [word3, chiInstruction, X86.xor3, rotzero]
  ac_rfl

private theorem cell4 (a : State) (rc : Lane) : word4 a rc = (round a rc)[4]! := by
  rw [roundAt _ _ _ (by decide)]
  change word4 a rc = ((a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 14 ^^^ ((~~~(a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 0) &&& (a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 44))
  simp only [word4, chiInstruction, X86.xor3, rotzero]
  ac_rfl

private theorem cell5 (a : State) (rc : Lane) : word5 a rc = (round a rc)[5]! := by
  rw [roundAt _ _ _ (by decide)]
  change word5 a rc = ((a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 28 ^^^ ((~~~(a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 20) &&& (a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 3))
  simp only [word5, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell6 (a : State) (rc : Lane) : word6 a rc = (round a rc)[6]! := by
  rw [roundAt _ _ _ (by decide)]
  change word6 a rc = ((a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 20 ^^^ ((~~~(a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 3) &&& (a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 45))
  simp only [word6, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell7 (a : State) (rc : Lane) : word7 a rc = (round a rc)[7]! := by
  rw [roundAt _ _ _ (by decide)]
  change word7 a rc = ((a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 3 ^^^ ((~~~(a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 45) &&& (a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 61))
  simp only [word7, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell8 (a : State) (rc : Lane) : word8 a rc = (round a rc)[8]! := by
  rw [roundAt _ _ _ (by decide)]
  change word8 a rc = ((a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 45 ^^^ ((~~~(a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 61) &&& (a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 28))
  simp only [word8, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell9 (a : State) (rc : Lane) : word9 a rc = (round a rc)[9]! := by
  rw [roundAt _ _ _ (by decide)]
  change word9 a rc = ((a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 61 ^^^ ((~~~(a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 28) &&& (a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 20))
  simp only [word9, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell10 (a : State) (rc : Lane) : word10 a rc = (round a rc)[10]! := by
  rw [roundAt _ _ _ (by decide)]
  change word10 a rc = ((a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 1 ^^^ ((~~~(a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 6) &&& (a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 25))
  simp only [word10, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell11 (a : State) (rc : Lane) : word11 a rc = (round a rc)[11]! := by
  rw [roundAt _ _ _ (by decide)]
  change word11 a rc = ((a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 6 ^^^ ((~~~(a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 25) &&& (a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 8))
  simp only [word11, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell12 (a : State) (rc : Lane) : word12 a rc = (round a rc)[12]! := by
  rw [roundAt _ _ _ (by decide)]
  change word12 a rc = ((a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 25 ^^^ ((~~~(a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 8) &&& (a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 18))
  simp only [word12, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell13 (a : State) (rc : Lane) : word13 a rc = (round a rc)[13]! := by
  rw [roundAt _ _ _ (by decide)]
  change word13 a rc = ((a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 8 ^^^ ((~~~(a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 18) &&& (a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 1))
  simp only [word13, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell14 (a : State) (rc : Lane) : word14 a rc = (round a rc)[14]! := by
  rw [roundAt _ _ _ (by decide)]
  change word14 a rc = ((a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 18 ^^^ ((~~~(a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 1) &&& (a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 6))
  simp only [word14, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell15 (a : State) (rc : Lane) : word15 a rc = (round a rc)[15]! := by
  rw [roundAt _ _ _ (by decide)]
  change word15 a rc = ((a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 27 ^^^ ((~~~(a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 36) &&& (a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 10))
  simp only [word15, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell16 (a : State) (rc : Lane) : word16 a rc = (round a rc)[16]! := by
  rw [roundAt _ _ _ (by decide)]
  change word16 a rc = ((a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 36 ^^^ ((~~~(a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 10) &&& (a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 15))
  simp only [word16, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell17 (a : State) (rc : Lane) : word17 a rc = (round a rc)[17]! := by
  rw [roundAt _ _ _ (by decide)]
  change word17 a rc = ((a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 10 ^^^ ((~~~(a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 15) &&& (a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 56))
  simp only [word17, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell18 (a : State) (rc : Lane) : word18 a rc = (round a rc)[18]! := by
  rw [roundAt _ _ _ (by decide)]
  change word18 a rc = ((a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 15 ^^^ ((~~~(a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 56) &&& (a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 27))
  simp only [word18, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell19 (a : State) (rc : Lane) : word19 a rc = (round a rc)[19]! := by
  rw [roundAt _ _ _ (by decide)]
  change word19 a rc = ((a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 56 ^^^ ((~~~(a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 27) &&& (a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 36))
  simp only [word19, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell20 (a : State) (rc : Lane) : word20 a rc = (round a rc)[20]! := by
  rw [roundAt _ _ _ (by decide)]
  change word20 a rc = ((a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 62 ^^^ ((~~~(a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 55) &&& (a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 39))
  simp only [word20, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell21 (a : State) (rc : Lane) : word21 a rc = (round a rc)[21]! := by
  rw [roundAt _ _ _ (by decide)]
  change word21 a rc = ((a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 55 ^^^ ((~~~(a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 39) &&& (a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 41))
  simp only [word21, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell22 (a : State) (rc : Lane) : word22 a rc = (round a rc)[22]! := by
  rw [roundAt _ _ _ (by decide)]
  change word22 a rc = ((a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 39 ^^^ ((~~~(a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 41) &&& (a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 2))
  simp only [word22, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell23 (a : State) (rc : Lane) : word23 a rc = (round a rc)[23]! := by
  rw [roundAt _ _ _ (by decide)]
  change word23 a rc = ((a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 41 ^^^ ((~~~(a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 2) &&& (a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 62))
  simp only [word23, chiInstruction, X86.xor3]
  ac_rfl

private theorem cell24 (a : State) (rc : Lane) : word24 a rc = (round a rc)[24]! := by
  rw [roundAt _ _ _ (by decide)]
  change word24 a rc = ((a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 2 ^^^ ((~~~(a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 62) &&& (a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 55))
  simp only [word24, chiInstruction, X86.xor3]
  ac_rfl

theorem round_fips (a : State) (rc : Lane) : roundCode a rc = round a rc := by
  apply ext25
  · rfl
  · simp only [round, Id.run, pure, Array.size_ofFn]
  · intro i hi
    interval_cases i
    · exact cell0 a rc
    · exact cell1 a rc
    · exact cell2 a rc
    · exact cell3 a rc
    · exact cell4 a rc
    · exact cell5 a rc
    · exact cell6 a rc
    · exact cell7 a rc
    · exact cell8 a rc
    · exact cell9 a rc
    · exact cell10 a rc
    · exact cell11 a rc
    · exact cell12 a rc
    · exact cell13 a rc
    · exact cell14 a rc
    · exact cell15 a rc
    · exact cell16 a rc
    · exact cell17 a rc
    · exact cell18 a rc
    · exact cell19 a rc
    · exact cell20 a rc
    · exact cell21 a rc
    · exact cell22 a rc
    · exact cell23 a rc
    · exact cell24 a rc

theorem permutation_fips (a : State) : permutation a = permute a := by
  unfold permutation permute
  rw [show roundCode=round from funext fun a => funext (round_fips a)]
  rfl
end slhdsa.KeccakAsm
