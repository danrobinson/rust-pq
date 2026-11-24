import Kbulk.Funs
import Koriented.Permutation
import Shakeabs.Word
open Aeneas Aeneas.Std Result ControlFlow
open Spec.Keccak
namespace slhdsa.Oriented.Bulk
open KbulkRust.shake256
set_option maxHeartbeats 2000000

private theorem rotateXor (a b : Lane) (r : Nat) :
    (a ^^^ b).rotateLeft r = a.rotateLeft r ^^^ b.rotateLeft r := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_xor]
  split <;> rfl

theorem updateWord (a : Array U64 25#usize) (idx : Usize) (word : U64) (hi : idx.val < 25) :
    let off := oriented.OFF.val[idx.val]!
    let x := a.val[idx.val]! ^^^ core.num.U64.rotate_right word off
    decode (a.set idx x) = (decode a).setIfInBounds idx.val ((decode a)[idx.val]! ^^^ word.bv) := by
  dsimp only
  have offEq : oriented.OFF = KorientedRust.shake256.oriented.OFF := by
    unfold oriented.OFF KorientedRust.shake256.oriented.OFF; rfl
  rw [offEq]
  apply ext25 _ _ (by simp [decode]) (by simp [decode])
  intro j hj
  rw [decodedAt _ _ hj]
  conv_rhs => rw [getElem!_pos _ j (by simpa [decode] using hj),_root_.Array.getElem_setIfInBounds (show j < (decode a).size by simpa [decode] using hj)]
  rw [Array.set_val_eq,getElem!_pos _ _ (by simp; omega),List.getElem_set]
  split
  · subst j
    rw [decodedAt _ _ hi]
    let r := KorientedRust.shake256.oriented.OFF.val[idx.val]!.val
    change (a.val[idx.val]!.bv ^^^ word.bv.rotateRight r).rotateLeft r =
      a.val[idx.val]!.bv.rotateLeft r ^^^ word.bv
    rw [rotateXor,rotateInverse]
  · rename_i ne
    rw [← getElem!_pos a.val j (by simpa using hj),
      ← getElem!_pos (decode a) j (by simpa [decode] using hj),decodedAt _ _ hj]

end slhdsa.Oriented.Bulk
