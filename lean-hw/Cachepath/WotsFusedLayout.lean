import Cachepath.WotsFusedRound
open Aeneas Aeneas.Std Result
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open ShakeBatch

private theorem low_addr (x : U32) :
    Spec.Keccak.laneBytes 0 (Spec.toByte x.val 4 ++ Spec.toByte 0 4) = addressLow x := by
  change Spec.Keccak.laneBytes 0 (Spec.toByte x.bv.toNat 4 ++ _) = _
  rw [toByte4]
  change Spec.Keccak.laneBytes 0 (_ ++ [0,0,0,0]) = _
  simp only [List.cons_append,List.nil_append,Spec.Keccak.laneBytes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [addressLow,BitVec.getLsbD_xor,BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

theorem packed_address (a : address.Adrs) (chain index : U32) (k : Nat) (hk : k<4) :
    addressWord {a with word2:=chain,word3:=index} k =
      if k=3 then addressLow chain ||| wordTag index else addressWord a k := by
  rw [tagged_address {a with word2:=chain} index k hk]
  let front := Spec.toByte a.layer.val 4 ++ Spec.toByte a.tree.val 12 ++ Spec.toByte a.typ.val 4 ++ Spec.toByte a.keypair.val 4
  have len : front.length=24 := by simp [front,Spec.toByte]
  have bytes' (x y : U32) : (adrsS {a with word2:=x,word3:=y}).bytes =
      front ++ (Spec.toByte x.val 4 ++ Spec.toByte y.val 4) := by simp [front,adrsS,Spec.Adrs.bytes,List.append_assoc]
  by_cases last : k=3
  · subst k
    simp only [ite_true,addressWord,bytes',show 3*8=24 by decide,← len,List.drop_left]
    have len8 : (Spec.toByte chain.val 4 ++ Spec.toByte 0 4).length=8 := by simp [Spec.toByte]
    change Spec.Keccak.laneBytes 0 ((Spec.toByte chain.val 4 ++ Spec.toByte 0 4).take 8) ||| _ = _
    rw [List.take_of_length_le (le_of_eq len8),low_addr]
  · rw [ite_eq_right last,ite_eq_right last]
    have raw : (adrsS a).bytes = front ++ (Spec.toByte a.word2.val 4 ++ Spec.toByte a.word3.val 4) := by
      simpa using bytes' a.word2 a.word3
    have drop (tail : Spec.Bytes) : ((front ++ tail).drop (k*8)).take 8 = (front.drop (k*8)).take 8 := by
      rw [List.drop_append_of_le_length (by omega),List.take_append_of_le_length (by simp;omega)]
    simp only [addressWord,raw,bytes',drop]

def baseWord {N : Usize} (seed : Array U8 N) (a : address.Adrs) (k : Nat) :=
  let raw := initialWord seed a (2*N.val+32) k
  if k=16 then raw ||| 0x8000000000000000 else raw

theorem packed_layout {N : Usize} (seed value : Array U8 N) (a : address.Adrs) (chain index : U32)
    (small : N.val≤32) (align : N.val%8=0) (k : Nat) :
    (if N.val/8+4 ≤ k ∧ k < N.val/8+4+N.val/8 then inputWord value.val (k-(N.val/8+4))
     else if k=N.val/8+4-1 then addressLow chain ||| wordTag index else baseWord seed a k) =
      Spec.Keccak.paddedWord (bytes seed.val ++ ((adrsS {a with word2:=chain,word3:=index}).bytes ++ bytes value.val)) k := by
  rw [← short_layout seed _ _ small align]
  unfold baseWord initialWord
  have size : (2*N.val+32)/8=2*(N.val/8)+4 := by omega
  rw [size]
  by_cases addr : N.val/8 ≤ k ∧ k < N.val/8+4
  · have localIndex : k-N.val/8<4 := by omega
    have noPay : ¬(N.val/8+4 ≤ k ∧ k<N.val/8+4+N.val/8) := by omega
    have beforePad : k≠2*(N.val/8)+4 := by omega
    have beforeFinal : k≠16 := by omega
    simp only [noPay,addr,beforePad,beforeFinal,ite_false,packed_address a chain index _ localIndex]
    by_cases last : k=N.val/8+4-1
    · simp [last]
    · simp only [ite_eq_right last,ite_eq_right (show k-N.val/8≠3 by omega)]
  · have notLast : k≠N.val/8+4-1 := by omega
    simp only [addr,notLast,ite_false]

end slhdsa.cache.builder.nativeShake.Vector.Fused
