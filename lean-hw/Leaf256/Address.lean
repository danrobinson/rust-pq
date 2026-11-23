import Leaf256.Payload
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256

private theorem cons_tail (x : Spec.Byte) (xs : Spec.Bytes) (k : Nat) (hk : 0 < k) :
    (x::xs)[k]! = xs[k-1]! := by
  cases k <;> simp_all [List.getElem!_cons_succ]

theorem type_word (fromType toType : Spec.Byte) (head tail : Spec.Bytes) (hh : head.length = 9) (k : Nat) :
    withType (fun t => word (head ++ (fromType::tail)) (4*t)) (((fromType ^^^ toType).setWidth 32) <<< 16) k =
      word (head ++ (toType::tail)) (4*k) := by
  by_cases lo : k < 2
  · simp (disch := omega) only [withType,if_neg,word,List.getElem!_append_left]
  by_cases hi : 2 < k
  · simp (disch := omega) only [withType,if_neg,word,List.getElem!_append_right,hh,cons_tail]
  have eq : k = 2 := by omega
  subst k
  simp (disch := omega) only [withType,↓reduceIte,word,List.getElem!_append_left,List.getElem!_append_right,
    hh,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,List.getElem!_cons_zero,List.getElem!_cons_succ]
  ext bit h
  interval_cases bit <;> simp [BitVec.getElem_append (n := 24) (m := 8),BitVec.getElem_append (n := 16) (m := 8),
    BitVec.getElem_append (n := 8) (m := 8),BitVec.getElem_setWidth,BitVec.getElem_xor,BitVec.getElem_shiftLeft]
  all_goals grind

theorem typed_word (a : Spec.Adrs) (i : Nat) (sk : Spec.Bytes) (hsk : sk.length ≤ 33)
    (k : Nat) :
    withType (fun t => word (padFrom 64 ((prfAddress a i).compress ++ sk)) (4*t)) (((6#8 ^^^ BitVec.ofNat 8 a.typ).setWidth 32) <<< 16) k =
      word (padFrom 64 ((leafAddress a i).compress ++ sk)) (4*k) := by
  rw [padFrom_blk _ _ hsk,padFrom_blk _ _ hsk]
  let head9 := ((prfAddress a i).compress).take 9
  let tail := (prfAddress a i).compress.drop 10 ++ (sk ++ padTail sk.length)
  have h := type_word 6#8 (BitVec.ofNat 8 a.typ) head9 tail (by simp [head9,adrs_compress_length]) k
  have prf : (prfAddress a i).compress ++ (sk ++ padTail sk.length) = head9 ++ (6#8 :: tail) := by
    simp only [head9,tail,compress_eq]; rfl
  have leaf : (leafAddress a i).compress ++ (sk ++ padTail sk.length) = head9 ++ (BitVec.ofNat 8 a.typ :: tail) := by
    simp only [head9,tail,compress_eq,leafAddress,prfAddress,Spec.Adrs.setTypeAndClear]; rfl
  rw [prf,leaf]; exact h

end slhdsa.X86.Leaf
