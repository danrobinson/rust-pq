import Gather512.Memory
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather

def flat {L : Usize} (rows : List (Array U8 L)) := rows.flatMap (·.val)
@[simp] theorem flat_length {L : Usize} (rows : List (Array U8 L)) :
    (flat rows).length = rows.length * L.val := by
  induction rows with
  | nil => simp [flat]
  | cons a xs ih => simp [flat, Nat.add_mul, Nat.add_comm]

theorem flat_byte {L : Usize} (rows : List (Array U8 L)) (j off : Nat) (hj : j < rows.length) (ho : off < L.val) :
    (flat rows)[j*L.val+off]! = rows[j]!.val[off]! := by
  induction rows generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero =>
      change (a.val ++ flat xs)[0*L.val+off]! = a.val[off]!
      simp only [Nat.zero_mul,Nat.zero_add,List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa using ho)]
    | succ j =>
      change (a.val ++ flat xs)[(j+1)*L.val+off]! = xs[j]!.val[off]!
      rw [← ih j (by simpa using hj)]
      simp only [List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp [Nat.succ_mul]; omega)]
      rw [show (j+1)*L.val+off-a.val.length = j*L.val+off by simp [Nat.add_mul]; omega]

theorem flat_word {L : Usize} (rows : List (Array U8 L)) (j off : Nat) (hj : j < rows.length) (ho : off+8 ≤ L.val) :
    Spec.SHA512.word (bytes (flat rows)) (j*L.val+off) = Spec.SHA512.word (bytes rows[j]!.val) off := by
  unfold Spec.SHA512.word
  have hlen : j*L.val+off+8 ≤ (flat rows).length := by
    rw [flat_length]
    calc
      _ ≤ (j+1)*L.val := by rw [Nat.add_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hj
  repeat rw [bytes_getElem! _ _ (by scalar_tac)]
  simp (disch := scalar_tac) only [← getElem!_pos, Nat.add_assoc, flat_byte]

#print axioms flat_word
end slhdsa.X86.S512.Gather
