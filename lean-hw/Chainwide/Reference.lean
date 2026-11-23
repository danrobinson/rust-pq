import Chainwide.Layout
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open Spec.SHA256

structure Lane where
  head : Spec.Bytes
  initial : Spec.Bytes
  tail : Spec.Bytes
  state : List Word
  first : Nat

def laneOf (n : Nat) (state : List Word) (row : Spec.Bytes) (start : Nat) : Lane :=
  ⟨row.take 18,(row.drop 22).take n,row.drop (22+n),state,start⟩

def Lane.value (p : Lane) (n : Nat) : Nat → Spec.Bytes
  | 0 => p.initial
  | t+1 => (ser (Spec.SHA256.compress p.state (packet p.head (BitVec.ofNat 32 (p.first+t)) (p.value n t) p.tail))).take n

def Lane.hash (p : Lane) (n t : Nat) :=
  Spec.SHA256.compress p.state (packet p.head (BitVec.ofNat 32 (p.first+t)) (p.value n t) p.tail)

theorem value_length (p : Lane) (n t : Nat) (hn : n ≤ 32) (hi : p.initial.length = n) : (p.value n t).length = n := by
  cases t with
  | zero => exact hi
  | succ t => simp [Lane.value,ser_length,sha_compress_length,hn]

private theorem replace_counter (head old value tail : Spec.Bytes) (hh : head.length = 18) (ho : old.length=4)
    (ctr : Nat) : (head ++ (old ++ (value ++ tail))).take 18 ++ Spec.toByte ctr 4 ++
      (head ++ (old ++ (value ++ tail))).drop 22 = head ++ (Spec.toByte ctr 4 ++ (value ++ tail)) := by
  have h := List.take_left (l₁ := head) (l₂ := old ++ (value ++ tail))
  rw [hh] at h
  rw [h,List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,hh]
  have d := List.drop_append_length (l₁ := old) (l₂ := value ++ tail)
  rw [ho] at d
  simp only [Nat.reduceSub,d,List.append_assoc]

theorem step_packet (head old value tail : Spec.Bytes) (st : List Word) (n ctr : Nat)
    (hh : head.length = 18) (ho : old.length = 4) (hv : value.length = n) (hc : ctr < 2^32) :
    stepBlock n st (head ++ (old ++ (value ++ tail))) ctr =
      packet head (BitVec.ofNat 32 ctr) ((ser (Spec.SHA256.compress st
        (packet head (BitVec.ofNat 32 ctr) value tail))).take n) tail := by
  unfold stepBlock
  rw [replace_counter _ _ _ _ hh ho]
  simp only [packet,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc]
  let pre := head ++ Spec.toByte ctr 4
  have len : pre.length = 22 := by simp [pre,hh,Spec.toByte]
  have h := List.take_left (l₁ := pre) (l₂ := value ++ tail)
  rw [len] at h
  have hd := List.drop_append_length (l₁ := value) (l₂ := tail)
  rw [hv] at hd
  have before : head ++ (Spec.toByte ctr 4 ++ (value ++ tail)) = pre ++ (value ++ tail) := by simp [pre,List.append_assoc]
  rw [before,h,List.drop_append,len,List.drop_eq_nil_of_le (by omega),List.nil_append,
    show 22+n-22=n by omega,hd]
  simp [pre,List.append_assoc]

theorem input_parts (row : Spec.Bytes) (n : Nat) (len : row.length = 64) (hn : n ≤ 32) :
    row = row.take 18 ++ (((row.drop 18).take 4) ++ ((row.drop 22).take n ++ row.drop (22+n))) := by
  have a := List.take_append_drop n (row.drop 22)
  have b := List.take_append_drop 4 (row.drop 18)
  rw [List.drop_drop] at a b
  rw [a,b,List.take_append_drop]

theorem portable_history (row : Spec.Bytes) (st : List Word) (n first t : Nat)
    (len : row.length = 64) (hn : n ≤ 32) (limit : first+t < 2^32) :
    let p := laneOf n st row first
    runBlock n st row first (first+(t+1)) =
      packet p.head (BitVec.ofNat 32 (first+t)) (p.value n (t+1)) p.tail := by
  induction t with
  | zero =>
    simp only
    rw [runBlock_one]
    conv => lhs; arg 3; rw [input_parts row n len hn]
    rw [step_packet _ _ _ _ _ _ _ (by simp [len]) (by simp [len]) (by simp [len]; omega) (by omega)]
    rfl
  | succ t ih =>
    simp only
    rw [runBlock_succ,ih (by omega)]
    unfold packet
    rw [step_packet _ _ _ _ _ _ _ (by simp [laneOf,len]) (by simp [Spec.toByte])
      (value_length _ _ _ hn (by simp [laneOf,len]; omega)) (by omega)]
    rfl

end slhdsa.X86.Chain
