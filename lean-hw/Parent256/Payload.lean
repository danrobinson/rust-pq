import Parent256.Pack
import Leaf256.Payload
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
open Spec.SHA256

def children (rows : Slice (Array U8 16#usize)) (i : Nat) :=
  bytes rows.val[2*i]!.val ++ bytes rows.val[2*i+1]!.val

theorem child_word (rows : Slice (Array U8 16#usize)) (i k : Nat) (hk : k < 8) :
    childWord rows i k = word (children rows i) (4*k) := by
  unfold childWord children word
  have len : (bytes rows.val[2*i]!.val).length = 16 := by simp
  by_cases h : k < 4
  · simp (disch := omega) only [show k/4=0 by omega,show k%4=k by omega,
      Nat.add_zero,List.getElem!_append_left]
  · simp (disch := omega) only [show k/4=1 by omega,List.getElem!_append_right,len]
    interval_cases k <;> rfl

def childWords (rows : Slice (Array U8 16#usize)) (i : Nat) :=
  List.ofFn fun k : Fin 8 => childWord rows i k.val

theorem serialize_children (rows : Slice (Array U8 16#usize)) (i : Nat) :
    ser (childWords rows i) = children rows i := by
  have len : (children rows i).length = 32 := by simp [children]
  have n : (childWords rows i).length = 8 := by simp [childWords]
  apply List.ext_getElem
  · rw [ser_length,n,len]
  · intro k hk hk'
    have small : k < 32 := len ▸ hk'
    rw [← getElem!_pos (ser (childWords rows i)) k hk,← getElem!_pos (children rows i) k hk',Digest.ser_byte _ _ (by omega)]
    rw [show (childWords rows i)[k/4]! = childWord rows i (k/4) by
      rw [getElem!_pos (childWords rows i) _ (by omega)]
      exact List.getElem_ofFn ..,child_word _ _ _ (by omega)]
    let b := children rows i
    change (word b (4*(k/4))).extractLsb' _ _ = b[k]!
    rcases (by omega : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3) with h|h|h|h
    all_goals rw [h]; unfold word
    · rw [show 4*(k/4) = k by omega]; bv_decide
    · rw [show 4*(k/4)+1 = k by omega]; bv_decide
    · rw [show 4*(k/4)+2 = k by omega]; bv_decide
    · rw [show 4*(k/4)+3 = k by omega]; bv_decide


def template (A : Spec.Adrs) :=
  padFrom 64 ({A with word3 := 0}.compress ++ List.replicate 32 0#8)

def parentWords (base child : Nat → Word) (idx : Word) (k : Nat) :=
  if k = 4 then base k ||| (idx >>> 16)
  else if k = 5 then (idx <<< 16) ||| (child 0 >>> 16)
  else if 6 ≤ k ∧ k < 13 then (child (k-6) <<< 16) ||| (child (k-5) >>> 16)
  else if k = 13 then (child 7 <<< 16) ||| base k
  else base k

private theorem last_template_word (A : Spec.Adrs) :
    word (template A) (4*13) = 0x8000 := by
  unfold template
  rw [padFrom_blk _ _ (by simp)]
  have hlen := adrs_compress_length ({A with word3 := 0})
  simp (disch := omega) only [word,Nat.reduceMul,Nat.reduceAdd,
    List.getElem!_append_right,adrs_compress_length,Nat.reduceSub,List.length_replicate]
  rfl

private theorem patched_word (A : Spec.Adrs) (idx : Word) (k : Nat) :
    Leaf.prfWords (fun t => word (template A) (4*t)) idx k =
      word ({A with word3 := idx.toNat}.compress ++ (List.replicate 32 0#8 ++ padTail 32)) (4*k) := by
  unfold template
  rw [padFrom_blk ({A with word3 := 0}) (List.replicate 32 0#8) (by simp)]
  simp only [List.length_replicate,
    compress_word3 A 0,compress_word3 A idx.toNat,List.append_assoc]
  exact Leaf.index_word _ _ (by simp [adrs_compress_length]) idx k

theorem message_layout (A : Spec.Adrs) (rows : Slice (Array U8 16#usize)) (i index : Nat)
    (hi : index < 2^32) :
    Leaf.blockOf (parentWords (fun t => word (template A) (4*t)) (childWord rows i) (BitVec.ofNat 32 index)) =
    padFrom 64 ({A with word3 := index}.compress ++ children rows i) := by
  let idx := BitVec.ofNat 32 index
  let base := fun t => word (template A) (4*t)
  let zeros := List.replicate 32 0#8
  let addr := {A with word3 := index}
  let ws := childWords rows i
  have len : (children rows i).length = 32 := by simp [children]
  have nw : ws.length = 8 := List.length_ofFn
  have cw (k : Nat) (hk : k < 8) : ws[k]! = childWord rows i k := by
    rw [getElem!_pos ws k (by omega)]
    exact List.getElem_ofFn ..
  have patched (k : Nat) : Leaf.prfWords base idx k = word (addr.compress ++ (zeros ++ padTail 32)) (4*k) := by
    have h := patched_word A idx k
    have hidx : idx.toNat = index := Nat.mod_eq_of_lt hi
    rw [hidx] at h
    exact h
  apply Eq.trans _ (Leaf.block_words_inverse _ (padFrom_blk_length _ _ (by omega)))
  apply Leaf.block_congr
  intro k hk
  rw [padFrom_blk _ _ (by omega),len]
  have payload := Leaf.payload_word addr.compress zeros (padTail 32) ws 32 k (adrs_compress_length _) (by simp [zeros]) nw (by simp)
  rw [show (ser ws).take 32 = children rows i by rw [serialize_children]; exact List.take_of_length_le (by omega)] at payload
  rw [← payload]
  unfold Leaf.payloadWord
  simp only [← patched]
  have last : base 13 = 0x8000 := last_template_word A
  change parentWords base (childWord rows i) idx k = _
  interval_cases k <;> simp [parentWords,Leaf.prfWords,Leaf.interior,cw,last] <;>
    first | rfl | (leaf_bits <;> rfl)

end slhdsa.X86.Parent
