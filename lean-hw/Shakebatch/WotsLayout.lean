import Shakebatch.WotsTag
import Shakebatch.Short
import Slhdsa.Proofs.Sha256
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

private theorem taggedWord (x y : U32) :
    Spec.Keccak.laneBytes 0 (Spec.toByte x.val 4 ++ Spec.toByte y.val 4) =
      Spec.Keccak.laneBytes 0 (Spec.toByte x.val 4 ++ Spec.toByte 0 4) ||| wordTag y := by
  change Spec.Keccak.laneBytes 0 (Spec.toByte x.bv.toNat 4 ++ Spec.toByte y.bv.toNat 4) = _
  rw [toByte4,toByte4]
  change _ = Spec.Keccak.laneBytes 0 (Spec.toByte x.bv.toNat 4 ++ _) ||| _
  rw [toByte4]
  change _ = Spec.Keccak.laneBytes 0 (_ ++ [0,0,0,0]) ||| _
  simp only [List.cons_append,List.nil_append,Spec.Keccak.laneBytes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [wordTag,BitVec.getLsbD_or,BitVec.getLsbD_xor,BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth',BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]


theorem tagged_address (addr : address.Adrs) (index : U32) (k : Nat) (hk : k<4) :
    addressWord {addr with word3:=index} k = if k=3 then
      addressWord {addr with word3:=0#u32} k ||| wordTag index else addressWord {addr with word3:=0#u32} k := by
  let front := Spec.toByte addr.layer.val 4 ++ Spec.toByte addr.tree.val 12 ++
    Spec.toByte addr.typ.val 4 ++ Spec.toByte addr.keypair.val 4
  have len : front.length=24 := by simp [front,Spec.toByte]
  have source (w : U32) : (adrsS {addr with word3:=w}).bytes =
      front ++ (Spec.toByte addr.word2.val 4 ++ Spec.toByte w.val 4) := by simp [front,adrsS,Spec.Adrs.bytes,List.append_assoc]
  unfold addressWord
  rw [source,source]
  by_cases last : k=3
  · subst k
    simp only [ite_true,show 3*8=24 by decide,← len,List.drop_left]
    have size (w : Nat) : (Spec.toByte addr.word2.val 4 ++ Spec.toByte w 4).length=8 := by simp [Spec.toByte]
    simp only [List.take_of_length_le (le_of_eq (size index.val)),List.take_of_length_le (le_of_eq (size 0))]
    exact taggedWord addr.word2 index
  · rw [if_neg last]
    have cut : k*8+8 ≤ front.length := by omega
    have drop (tail : Spec.Bytes) : ((front ++ tail).drop (k*8)).take 8 = (front.drop (k*8)).take 8 := by
      rw [List.drop_append_of_le_length (by omega),List.take_append_of_le_length (by simp;omega)]
    rw [drop,drop]

def payloadLayout {N : Usize} (seed : Array U8 N) (a : address.Adrs) (value : Array U8 N) (k : Nat) :=
  let off := N.val/8+4
  if off ≤ k ∧ k < off+N.val/8 then inputWord value.val (k-off)
  else let w := initialWord seed a (2*N.val+32) k; if k=16 then w ||| 0x8000000000000000 else w

theorem tagged_layout {N : Usize} (seed : Array U8 N) (a : address.Adrs) (value : Array U8 N)
    (index : U32) (bound : N.val ≤ 32) (align : N.val%8=0) (k : Nat) :
    (if k=N.val/8+4-1 then payloadLayout seed {a with word3:=0#u32} value k ||| wordTag index
     else payloadLayout seed {a with word3:=0#u32} value k) =
      Spec.Keccak.paddedWord (bytes seed.val ++ ((adrsS {a with word3:=index}).bytes ++ bytes value.val)) k := by
  rw [← short_layout seed _ _ bound align k]
  change _ = payloadLayout seed {a with word3:=index} value k
  unfold payloadLayout initialWord
  have size : (2*N.val+32)/8=2*(N.val/8)+4 := by omega
  rw [size]
  by_cases addr : N.val/8 ≤ k ∧ k < N.val/8+4
  · have localIndex : k-N.val/8<4 := by omega
    have noPay : ¬(N.val/8+4 ≤ k ∧ k<N.val/8+4+N.val/8) := by omega
    have beforePad : k≠2*(N.val/8)+4 := by omega
    have beforeFinal : k≠16 := by omega
    simp only [noPay,addr,beforePad,beforeFinal,ite_true,ite_false,tagged_address a index _ localIndex]
    by_cases last : k=N.val/8+4-1
    · simp only [last,and_self,ite_true,show (N.val/8+4-1)-N.val/8=3 by omega]
    · simp only [last,show k-N.val/8≠3 by omega,ite_false]
  · have notLast : k≠N.val/8+4-1 := by omega
    simp only [addr,notLast,ite_false]

end slhdsa.ShakeBatch
