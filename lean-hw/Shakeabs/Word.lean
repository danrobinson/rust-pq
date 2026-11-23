import Shakeabs.Funs
import Keccakscalar.Proof
import Slhdsa.Proofs.Shake256
import Spec.ShakeWords
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake
open Keccak (words)
private theorem eight (b0 b1 b2 b3 b4 b5 b6 b7 : U8) :
    (core.num.U64.from_le_bytes (Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7])).bv =
      Spec.Keccak.laneBytes 0 [b0.bv,b1.bv,b2.bv,b3.bv,b4.bv,b5.bv,b6.bv,b7.bv] := by
  change (BitVec.fromLEBytes [b0.bv,b1.bv,b2.bv,b3.bv,b4.bv,b5.bv,b6.bv,b7.bv]).cast (by rfl) = _
  simp only [BitVec.fromLEBytes,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul,
    BitVec.cast_eq,bytes,List.map_cons,List.map_nil,Spec.Keccak.laneBytes]
  ext i hi
  interval_cases i <;> simp [BitVec.getElem_or,BitVec.getElem_shiftLeft,BitVec.getElem_setWidth,BitVec.getElem_xor]

theorem loaded (a : Array U8 8#usize) :
    (core.num.U64.from_le_bytes a).bv = Spec.Keccak.laneBytes 0 (bytes a.val) := by
  let xs := [a.val[0]!,a.val[1]!,a.val[2]!,a.val[3]!,a.val[4]!,a.val[5]!,a.val[6]!,a.val[7]!]
  have rebuild : a = Array.make 8#usize xs (by rfl) := by
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp [xs]
    · intro i hi _
      have lt : i < 8 := by simpa using hi
      interval_cases i <;> simp [xs,getElem!_pos]
  conv => lhs; rw [rebuild]
  rw [eight]
  congr 1
  exact congrArg (fun x : Array U8 8#usize => bytes x.val) rebuild.symm

theorem words_set {n : Usize} (a : Array U64 n) (i : Usize) (v : U64) :
    words (a.set i v) = (words a).setIfInBounds i.val v.bv := by
  apply _root_.Array.ext
  · simp [words]
  · intro j h1 h2
    simp only [words, Array.set_val_eq, List.getElem_toArray, List.getElem_map,
      List.getElem_set, _root_.Array.getElem_setIfInBounds]
    split <;> simp_all
end slhdsa.PlatformShake
