import Kgridbulk.Loads
open Aeneas Aeneas.Std Result
namespace slhdsa.Kgridbulk
private abbrev encode (w : U64) : List U8 := w.bv.toLEBytes.map fun b => ⟨b⟩

private theorem byteAt (ws : List U64) (n k : Nat) (hn : n < ws.length) (hk : k < 8) :
    (ws.flatMap encode)[8*n+k]! = (encode ws[n]!)[k]! := by
  induction ws generalizing n with
  | nil => simp at hn
  | cons w ws ih =>
    have len : (encode w).length=8 := by simp [encode]
    rw [List.flatMap_cons]
    cases n with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add,List.getElem!_cons_zero]
      exact List.getElem!_append_left _ _ _ (by omega)
    | succ n =>
      rw [List.getElem!_append_right _ _ _ (by omega),len,
        show 8*(n+1)+k-8=8*n+k by omega,List.getElem!_cons_succ]
      exact ih n (by simpa using hn)

private theorem packed (b : BitVec 64) :
    b.toLEBytes[7]! ++ b.toLEBytes[6]! ++ b.toLEBytes[5]! ++ b.toLEBytes[4]! ++
    b.toLEBytes[3]! ++ b.toLEBytes[2]! ++ b.toLEBytes[1]! ++ b.toLEBytes[0]! = b := by
  simp [BitVec.toLEBytes]
  all_goals bv_decide

private theorem decode (w : U64) : wordAt (encode w) 0 = w.bv := by
  have byte (i : Nat) (hi : i < 8) : (encode w)[i]!.bv = w.bv.toLEBytes[i]! := by
    rw [getElem!_pos _ i (by simpa [encode] using hi),
      getElem!_pos w.bv.toLEBytes i (by simpa using hi)]
    unfold encode
    rw [List.getElem_map]
  unfold wordAt GatherRust.core.core_arch.x86.littleWord
  simp only [Nat.zero_add,byte 0 (by decide),byte 1 (by decide),byte 2 (by decide),
    byte 3 (by decide),byte 4 (by decide),byte 5 (by decide),byte 6 (by decide),byte 7 (by decide)]
  exact packed w.bv

theorem readStateWord (ws : List U64) (n : Nat) (hn : n<ws.length) :
    wordAt (ws.flatMap encode) (8*n) = ws[n]!.bv := by
  rw [←decode ws[n]!]
  unfold wordAt GatherRust.core.core_arch.x86.littleWord
  simp only [Nat.zero_add]
  simp only [byteAt ws n 7 hn (by decide), byteAt ws n 6 hn (by decide),
    byteAt ws n 5 hn (by decide), byteAt ws n 4 hn (by decide), byteAt ws n 3 hn (by decide),
    byteAt ws n 2 hn (by decide), byteAt ws n 1 hn (by decide)]
  rw [show (ws.flatMap encode)[8*n]! = (encode ws[n]!)[0]! from
    by simpa only [Nat.add_zero] using byteAt ws n 0 hn (by decide)]
end slhdsa.Kgridbulk
