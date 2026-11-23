import Shakebatch.WotsOrderProgram
open Aeneas Aeneas.Std
namespace slhdsa.ShakeBatch.WotsOrder

/-- Elements with a smaller digit precede this bucket. Equal digits retain their input order. -/
def below (digits : List U32) (d : Nat) := digits.countP (fun x => decide (x.val<d))
def counted (digits : List U32) (n d : Nat) := (digits.take n).countP (fun x => decide (x.val=d))
def rank (digits : List U32) (i : Nat) :=
  below digits digits[i]!.val + counted digits i digits[i]!.val

theorem below_next (digits : List U32) (d : Nat) :
    below digits (d+1)=below digits d+counted digits digits.length d := by
  simp only [below,counted,List.take_length]
  induction digits with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons,decide_eq_true_eq]
    split_ifs <;> omega

theorem below_mono (digits : List U32) {a b : Nat} (le : a≤b) : below digits a ≤ below digits b :=
  List.countP_mono_left (by intro x _ h; simp only [decide_eq_true_eq] at h ⊢;omega)

theorem count_next (digits : List U32) (i d : Nat) (hi : i<digits.length) :
    counted digits (i+1) d = counted digits i d + (if digits[i]!.val=d then 1 else 0) := by
  rw [counted,List.take_succ_eq_append_getElem hi,List.countP_append]
  simp [counted,hi]

theorem count_mono (digits : List U32) (d : Nat) {a b : Nat} (h : a≤b) :
    counted digits a d ≤ counted digits b d := by
  unfold counted
  rw [show b=a+(b-a) by omega,List.take_add,List.countP_append]
  omega

theorem count_strict (digits : List U32) {a b : Nat} (ha : a<digits.length) (h : a<b) :
    counted digits a digits[a]!.val < counted digits b digits[a]!.val := by
  have mono := count_mono digits digits[a]!.val (show a+1≤b by omega)
  rw [count_next digits a _ ha,if_pos rfl] at mono
  omega

theorem in_bucket (ds : List U32) (i : Nat) (hi : i<ds.length) :
    below ds ds[i]!.val ≤ rank ds i ∧ rank ds i < below ds (ds[i]!.val+1) := by
  have less := count_strict ds hi hi
  simp only [rank,below_next]
  omega

theorem rank_lt (digits : List U32) (i : Nat) (hi : i<digits.length) : rank digits i < digits.length :=
  Nat.lt_of_lt_of_le (in_bucket digits i hi).2 List.countP_le_length

theorem rank_injective (ds : List U32) {i j : Nat} (hi : i<ds.length) (hj : j<ds.length) (same : rank ds i=rank ds j) : i=j := by
  have bi := in_bucket ds i hi
  have bj := in_bucket ds j hj
  have equal : ds[i]!.val=ds[j]!.val := by
    rcases lt_trichotomy ds[i]!.val ds[j]!.val with h|h|h
    · have clash := Nat.lt_of_lt_of_le bi.2 ((below_mono ds (Nat.succ_le_of_lt h)).trans bj.1);omega
    · exact h
    · have clash := Nat.lt_of_lt_of_le bj.2 ((below_mono ds (Nat.succ_le_of_lt h)).trans bi.1);omega
  unfold rank at same
  rw [equal] at same
  rcases lt_trichotomy i j with lt|eq|gt
  · have h := count_strict ds hi lt;rw [equal] at h;omega
  · exact eq
  · have h := count_strict ds hj gt;omega

end slhdsa.ShakeBatch.WotsOrder
