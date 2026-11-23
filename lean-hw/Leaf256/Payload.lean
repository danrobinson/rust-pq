import Leaf256.Layout
import Digest256.Fips
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256

def payloadWord (old : Nat → Word) (ws : List Word) (n k : Nat) : Word :=
  if k = 5 then (old k &&& 0xffff0000) ||| (ws[0]! >>> 16)
  else if k = 5+n/4 then (ws[n/4-1]! <<< 16) ||| (old k &&& 0xffff)
  else if 6 ≤ k ∧ k < 5+n/4 then interior ws[k-6]! ws[k-5]!
  else old k

private theorem serialized (ws : List Word) (n i : Nat) (hi : i < n) (hn : n ≤ 4*ws.length) :
    ((ser ws).take n)[i]! = ws[i/4]!.extractLsb' (8*(3-i%4)) 8 := by
  rw [List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt hi,← List.getElem!_eq_getElem?_getD]
  exact Digest.ser_byte ws i (by omega)

private theorem first_word (a b c d : Spec.Byte) (w : Word) :
    ((a ++ b ++ c ++ d) &&& 0xffff0000#32) ||| (w >>> 16) =
      a ++ b ++ w.extractLsb' 24 8 ++ w.extractLsb' 16 8 := by leaf_bits

private theorem last_word (a b c d : Spec.Byte) (w : Word) :
    (w <<< 16) ||| ((a ++ b ++ c ++ d) &&& 65535) =
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 ++ c ++ d := by leaf_bits

private theorem middle_word (x y : Word) :
    (x <<< 16) ||| (y >>> 16) = x.extractLsb' 8 8 ++ x.extractLsb' 0 8 ++
      y.extractLsb' 24 8 ++ y.extractLsb' 16 8 := by leaf_bits

theorem payload_word (head sk tail : Spec.Bytes) (ws : List Word) (n k : Nat)
    (hh : head.length = 22) (hs : sk.length = n) (hws : ws.length = 8)
    (shape : n = 16 ∨ n = 24 ∨ n = 32) :
    payloadWord (fun t => word (head ++ (sk ++ tail)) (4*t)) ws n k =
      word (head ++ ((ser ws).take n ++ tail)) (4*k) := by
  have len : ((ser ws).take n).length = n := by simp [ser_length,hws]; omega
  have small : n ≤ 4*ws.length := by omega
  by_cases before : k < 5
  · simp (disch := omega) only [payloadWord,if_neg,word,List.getElem!_append_left]
  by_cases after : 5+n/4 < k
  · simp (disch := omega) only [payloadWord,if_neg,word,List.getElem!_append_right,hh,len,hs]
  by_cases first : k = 5
  · subst k
    simp (disch := omega) only [payloadWord,if_pos,word,List.getElem!_append_left,List.getElem!_append_right,
      hh, Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,serialized ws n _ _ small,Nat.reduceDiv,Nat.reduceMod]
    simp only [↓reduceIte]; exact first_word _ _ _ _ _
  by_cases last : k = 5+n/4
  · subst k
    rcases shape with rfl|rfl|rfl <;>
      simp (disch := omega) only [payloadWord,if_neg,if_pos,↓reduceIte,word,
        Nat.reduceDiv,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Nat.reduceMod,
        List.getElem!_append_left,List.getElem!_append_right,hh,hs,len,serialized ws _ _ _ small] <;>
      exact last_word _ _ _ _ _
  have mid : 6 ≤ k ∧ k < 5+n/4 := by omega
  simp (disch := omega) only [payloadWord,if_neg,if_pos,word,List.getElem!_append_left,
    List.getElem!_append_right,hh,hs,len,serialized ws n _ _ small,interior]
  simp only [show (4*k-22)/4 = k-6 by omega,show (4*k+1-22)/4 = k-6 by omega,
    show (4*k+2-22)/4 = k-5 by omega,show (4*k+3-22)/4 = k-5 by omega,
    show (4*k-22)%4 = 2 by omega,show (4*k+1-22)%4 = 3 by omega,
    show (4*k+2-22)%4 = 0 by omega,show (4*k+3-22)%4 = 1 by omega]
  exact middle_word _ _

end slhdsa.X86.Leaf
