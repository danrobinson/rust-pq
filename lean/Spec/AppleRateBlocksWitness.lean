import Spec.ArmRateBlocks
import Spec.ShakeWords
import Spec.ArmSha3Binary
import Mathlib.Tactic.IntervalCases
namespace LinkedArmBulk
open Spec.Keccak
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
def word0 (a : State) (rc : Lane) : Lane := ((((a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 0) ^^^ ((~~~((a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 44)) &&& ((a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 43))) ^^^ rc)
theorem cell0 (a : State) (rc : Lane) : word0 a rc = (round a rc)[0]! := by
  rw [roundAt _ _ _ (by decide)]
  change word0 a rc = (a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 0 ^^^ ((~~~((a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 44)) &&& ((a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 43)) ^^^ rc
  unfold word0
  ac_rfl
def word1 (a : State) (rc : Lane) : Lane := (((a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 44) ^^^ ((~~~((a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 43)) &&& ((a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 21)))
theorem cell1 (a : State) (rc : Lane) : word1 a rc = (round a rc)[1]! := by
  rw [roundAt _ _ _ (by decide)]
  change word1 a rc = (a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 44 ^^^ ((~~~((a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 43)) &&& ((a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 21))
  unfold word1
  ac_rfl
def word2 (a : State) (rc : Lane) : Lane := (((a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 43) ^^^ ((~~~((a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 21)) &&& ((a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 14)))
theorem cell2 (a : State) (rc : Lane) : word2 a rc = (round a rc)[2]! := by
  rw [roundAt _ _ _ (by decide)]
  change word2 a rc = (a[12]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 43 ^^^ ((~~~((a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 21)) &&& ((a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 14))
  unfold word2
  ac_rfl
def word3 (a : State) (rc : Lane) : Lane := (((a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 21) ^^^ ((~~~((a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 14)) &&& ((a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 0)))
theorem cell3 (a : State) (rc : Lane) : word3 a rc = (round a rc)[3]! := by
  rw [roundAt _ _ _ (by decide)]
  change word3 a rc = (a[18]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 21 ^^^ ((~~~((a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 14)) &&& ((a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 0))
  unfold word3
  ac_rfl
def word4 (a : State) (rc : Lane) : Lane := (((a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 14) ^^^ ((~~~((a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 0)) &&& ((a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 44)))
theorem cell4 (a : State) (rc : Lane) : word4 a rc = (round a rc)[4]! := by
  rw [roundAt _ _ _ (by decide)]
  change word4 a rc = (a[24]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 14 ^^^ ((~~~((a[0]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 0)) &&& ((a[6]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 44))
  unfold word4
  ac_rfl
def word5 (a : State) (rc : Lane) : Lane := (((a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 28) ^^^ ((~~~((a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 20)) &&& ((a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 3)))
theorem cell5 (a : State) (rc : Lane) : word5 a rc = (round a rc)[5]! := by
  rw [roundAt _ _ _ (by decide)]
  change word5 a rc = (a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 28 ^^^ ((~~~((a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 20)) &&& ((a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 3))
  unfold word5
  ac_rfl
def word6 (a : State) (rc : Lane) : Lane := (((a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 20) ^^^ ((~~~((a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 3)) &&& ((a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 45)))
theorem cell6 (a : State) (rc : Lane) : word6 a rc = (round a rc)[6]! := by
  rw [roundAt _ _ _ (by decide)]
  change word6 a rc = (a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 20 ^^^ ((~~~((a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 3)) &&& ((a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 45))
  unfold word6
  ac_rfl
def word7 (a : State) (rc : Lane) : Lane := (((a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 3) ^^^ ((~~~((a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 45)) &&& ((a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 61)))
theorem cell7 (a : State) (rc : Lane) : word7 a rc = (round a rc)[7]! := by
  rw [roundAt _ _ _ (by decide)]
  change word7 a rc = (a[10]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 3 ^^^ ((~~~((a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 45)) &&& ((a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 61))
  unfold word7
  ac_rfl
def word8 (a : State) (rc : Lane) : Lane := (((a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 45) ^^^ ((~~~((a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 61)) &&& ((a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 28)))
theorem cell8 (a : State) (rc : Lane) : word8 a rc = (round a rc)[8]! := by
  rw [roundAt _ _ _ (by decide)]
  change word8 a rc = (a[16]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 45 ^^^ ((~~~((a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 61)) &&& ((a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 28))
  unfold word8
  ac_rfl
def word9 (a : State) (rc : Lane) : Lane := (((a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 61) ^^^ ((~~~((a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 28)) &&& ((a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 20)))
theorem cell9 (a : State) (rc : Lane) : word9 a rc = (round a rc)[9]! := by
  rw [roundAt _ _ _ (by decide)]
  change word9 a rc = (a[22]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 61 ^^^ ((~~~((a[3]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 28)) &&& ((a[9]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 20))
  unfold word9
  ac_rfl
def word10 (a : State) (rc : Lane) : Lane := (((a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 1) ^^^ ((~~~((a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 6)) &&& ((a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 25)))
theorem cell10 (a : State) (rc : Lane) : word10 a rc = (round a rc)[10]! := by
  rw [roundAt _ _ _ (by decide)]
  change word10 a rc = (a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 1 ^^^ ((~~~((a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 6)) &&& ((a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 25))
  unfold word10
  ac_rfl
def word11 (a : State) (rc : Lane) : Lane := (((a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 6) ^^^ ((~~~((a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 25)) &&& ((a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 8)))
theorem cell11 (a : State) (rc : Lane) : word11 a rc = (round a rc)[11]! := by
  rw [roundAt _ _ _ (by decide)]
  change word11 a rc = (a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 6 ^^^ ((~~~((a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 25)) &&& ((a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 8))
  unfold word11
  ac_rfl
def word12 (a : State) (rc : Lane) : Lane := (((a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 25) ^^^ ((~~~((a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 8)) &&& ((a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 18)))
theorem cell12 (a : State) (rc : Lane) : word12 a rc = (round a rc)[12]! := by
  rw [roundAt _ _ _ (by decide)]
  change word12 a rc = (a[13]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 25 ^^^ ((~~~((a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 8)) &&& ((a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 18))
  unfold word12
  ac_rfl
def word13 (a : State) (rc : Lane) : Lane := (((a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 8) ^^^ ((~~~((a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 18)) &&& ((a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 1)))
theorem cell13 (a : State) (rc : Lane) : word13 a rc = (round a rc)[13]! := by
  rw [roundAt _ _ _ (by decide)]
  change word13 a rc = (a[19]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 8 ^^^ ((~~~((a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 18)) &&& ((a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 1))
  unfold word13
  ac_rfl
def word14 (a : State) (rc : Lane) : Lane := (((a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 18) ^^^ ((~~~((a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 1)) &&& ((a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 6)))
theorem cell14 (a : State) (rc : Lane) : word14 a rc = (round a rc)[14]! := by
  rw [roundAt _ _ _ (by decide)]
  change word14 a rc = (a[20]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 18 ^^^ ((~~~((a[1]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 1)) &&& ((a[7]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 6))
  unfold word14
  ac_rfl
def word15 (a : State) (rc : Lane) : Lane := (((a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 27) ^^^ ((~~~((a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 36)) &&& ((a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 10)))
theorem cell15 (a : State) (rc : Lane) : word15 a rc = (round a rc)[15]! := by
  rw [roundAt _ _ _ (by decide)]
  change word15 a rc = (a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 27 ^^^ ((~~~((a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 36)) &&& ((a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 10))
  unfold word15
  ac_rfl
def word16 (a : State) (rc : Lane) : Lane := (((a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 36) ^^^ ((~~~((a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 10)) &&& ((a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 15)))
theorem cell16 (a : State) (rc : Lane) : word16 a rc = (round a rc)[16]! := by
  rw [roundAt _ _ _ (by decide)]
  change word16 a rc = (a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 36 ^^^ ((~~~((a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 10)) &&& ((a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 15))
  unfold word16
  ac_rfl
def word17 (a : State) (rc : Lane) : Lane := (((a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 10) ^^^ ((~~~((a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 15)) &&& ((a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 56)))
theorem cell17 (a : State) (rc : Lane) : word17 a rc = (round a rc)[17]! := by
  rw [roundAt _ _ _ (by decide)]
  change word17 a rc = (a[11]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 10 ^^^ ((~~~((a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 15)) &&& ((a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 56))
  unfold word17
  ac_rfl
def word18 (a : State) (rc : Lane) : Lane := (((a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 15) ^^^ ((~~~((a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 56)) &&& ((a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 27)))
theorem cell18 (a : State) (rc : Lane) : word18 a rc = (round a rc)[18]! := by
  rw [roundAt _ _ _ (by decide)]
  change word18 a rc = (a[17]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 15 ^^^ ((~~~((a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 56)) &&& ((a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 27))
  unfold word18
  ac_rfl
def word19 (a : State) (rc : Lane) : Lane := (((a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 56) ^^^ ((~~~((a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 27)) &&& ((a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 36)))
theorem cell19 (a : State) (rc : Lane) : word19 a rc = (round a rc)[19]! := by
  rw [roundAt _ _ _ (by decide)]
  change word19 a rc = (a[23]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 56 ^^^ ((~~~((a[4]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 27)) &&& ((a[5]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 36))
  unfold word19
  ac_rfl
def word20 (a : State) (rc : Lane) : Lane := (((a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 62) ^^^ ((~~~((a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 55)) &&& ((a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 39)))
theorem cell20 (a : State) (rc : Lane) : word20 a rc = (round a rc)[20]! := by
  rw [roundAt _ _ _ (by decide)]
  change word20 a rc = (a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 62 ^^^ ((~~~((a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 55)) &&& ((a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 39))
  unfold word20
  ac_rfl
def word21 (a : State) (rc : Lane) : Lane := (((a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 55) ^^^ ((~~~((a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 39)) &&& ((a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 41)))
theorem cell21 (a : State) (rc : Lane) : word21 a rc = (round a rc)[21]! := by
  rw [roundAt _ _ _ (by decide)]
  change word21 a rc = (a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 55 ^^^ ((~~~((a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 39)) &&& ((a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 41))
  unfold word21
  ac_rfl
def word22 (a : State) (rc : Lane) : Lane := (((a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!)) ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!))).rotateLeft 1)).rotateLeft 39) ^^^ ((~~~((a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 41)) &&& ((a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 2)))
theorem cell22 (a : State) (rc : Lane) : word22 a rc = (round a rc)[22]! := by
  rw [roundAt _ _ _ (by decide)]
  change word22 a rc = (a[14]! ^^^ ((a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!) ^^^ (a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!).rotateLeft 1)).rotateLeft 39 ^^^ ((~~~((a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 41)) &&& ((a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 2))
  unfold word22
  ac_rfl
def word23 (a : State) (rc : Lane) : Lane := (((a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!)) ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!))).rotateLeft 1)).rotateLeft 41) ^^^ ((~~~((a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 2)) &&& ((a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 62)))
theorem cell23 (a : State) (rc : Lane) : word23 a rc = (round a rc)[23]! := by
  rw [roundAt _ _ _ (by decide)]
  change word23 a rc = (a[15]! ^^^ ((a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!) ^^^ (a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!).rotateLeft 1)).rotateLeft 41 ^^^ ((~~~((a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 2)) &&& ((a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 62))
  unfold word23
  ac_rfl
def word24 (a : State) (rc : Lane) : Lane := (((a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ (a[10]! ^^^ a[15]! ^^^ a[20]!)) ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!))).rotateLeft 1)).rotateLeft 2) ^^^ ((~~~((a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ (a[11]! ^^^ a[16]! ^^^ a[21]!)) ^^^ ((a[3]! ^^^ a[8]! ^^^ (a[13]! ^^^ a[18]! ^^^ a[23]!))).rotateLeft 1)).rotateLeft 62)) &&& ((a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ (a[12]! ^^^ a[17]! ^^^ a[22]!)) ^^^ ((a[4]! ^^^ a[9]! ^^^ (a[14]! ^^^ a[19]! ^^^ a[24]!))).rotateLeft 1)).rotateLeft 55)))
theorem cell24 (a : State) (rc : Lane) : word24 a rc = (round a rc)[24]! := by
  rw [roundAt _ _ _ (by decide)]
  change word24 a rc = (a[21]! ^^^ ((a[0]! ^^^ a[5]! ^^^ a[10]! ^^^ a[15]! ^^^ a[20]!) ^^^ (a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!).rotateLeft 1)).rotateLeft 2 ^^^ ((~~~((a[2]! ^^^ ((a[1]! ^^^ a[6]! ^^^ a[11]! ^^^ a[16]! ^^^ a[21]!) ^^^ (a[3]! ^^^ a[8]! ^^^ a[13]! ^^^ a[18]! ^^^ a[23]!).rotateLeft 1)).rotateLeft 62)) &&& ((a[8]! ^^^ ((a[2]! ^^^ a[7]! ^^^ a[12]! ^^^ a[17]! ^^^ a[22]!) ^^^ (a[4]! ^^^ a[9]! ^^^ a[14]! ^^^ a[19]! ^^^ a[24]!).rotateLeft 1)).rotateLeft 55))
  unfold word24
  ac_rfl
def linkedRound (a : State) (rc : Lane) : State := #[word0 a rc, word1 a rc, word2 a rc, word3 a rc, word4 a rc, word5 a rc, word6 a rc, word7 a rc, word8 a rc, word9 a rc, word10 a rc, word11 a rc, word12 a rc, word13 a rc, word14 a rc, word15 a rc, word16 a rc, word17 a rc, word18 a rc, word19 a rc, word20 a rc, word21 a rc, word22 a rc, word23 a rc, word24 a rc]
theorem round_eq (a : State) (rc : Lane) : linkedRound a rc = round a rc := by
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
def instructions : List Nat := [3457245897, 2332688683, 3456247753, 2432704842, 3457894794, 3457493002, 3457644363, 3457166507, 1319902596, 3458164364, 3456512108, 1319968167, 3457950125, 3457365037, 3463089582, 3463154991, 3463220554, 3463286123, 3463024009, 3465413598, 3465499317, 3465172826, 3465261055, 3465136392, 3465252972, 3465130611, 3465475798, 3465498491, 3465154493, 3465542669, 3465210368, 3465256596, 3465143196, 3465460504, 3465122849, 3465441346, 3465533571, 3465201380, 3465225017, 3465152682, 3465225419, 3465110761, 3465436718, 3465542223, 3459930053, 1031799781, 3460262567, 3458760517, 3460178943, 3459610898, 3459665310, 3459996277, 3460132560, 3459020646, 3459462067, 3459514806, 3460059148, 3459805850, 3459081108, 3458217741, 3458402353, 3458468955, 3459846263, 1321148387, 3458294943, 3458336572, 1321082818, 1320296001, 3458805080, 3459130738, 3459201341, 3458874841, 3458935272, 1296092512, 1035994084, 1847598238, 1319574752]
def registers : List Nat := [30, 0, 5, 3, 1, 2, 21, 16, 6, 19, 22, 12, 26, 20, 13, 17, 27, 23, 31, 28, 24, 18, 29, 25, 8]
theorem decoded_eq (a : State) (rc : Lane) (s : Spec.ArmSha3Binary.Registers) :
    Spec.ArmSha3Binary.runBulk instructions registers a rc s = some (round a rc) := by
  rw [← round_eq]
  rfl
#print axioms decoded_eq
def linkedConstants : Array Lane := #[1,32898,9223372036854808714,9223372039002292224,32907,2147483649,9223372039002292353,9223372036854808585,138,136,2147516425,2147483658,2147516555,9223372036854775947,9223372036854808713,9223372036854808579,9223372036854808578,9223372036854775936,32778,9223372039002259466,9223372039002292353,9223372036854808704,2147483649,9223372039002292232]
def machineRound (scratch : Lane → Spec.ArmSha3Binary.Registers) (a : State) (rc : Lane) :=
  (Spec.ArmSha3Binary.runBulk instructions registers a rc (scratch rc)).getD #[]
theorem permutation_eq (a : State) (scratch : Lane → Spec.ArmSha3Binary.Registers) :
    linkedConstants.foldl (machineRound scratch) a = permute a := by
  have h : machineRound scratch = round := by
    funext a rc
    simp only [machineRound, decoded_eq, Option.getD_some]
  rw [h]
  rfl
#print axioms permutation_eq
theorem blocks_eq (scratch : Lane → Spec.ArmSha3Binary.Registers) (a : State)
    (size : a.size = 25) (words : List Spec.Bytes) (width : ∀ w ∈ words, w.length = 8) :
    let out := words.foldl (ArmRateBlocks.word (fun s => linkedConstants.foldl (machineRound scratch) s)) (a,0)
    (out.1, 8*out.2) = words.flatten.foldl feed (a,0) :=
  ArmRateBlocks.foldWords _ (fun s => permutation_eq s scratch) words width a size 0 (by decide)
#print axioms blocks_eq
end LinkedArmBulk
