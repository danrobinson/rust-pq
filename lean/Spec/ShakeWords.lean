import Spec.Shake256
import Mathlib.Data.List.Induction
namespace Spec.Keccak

/-- Little-endian contribution of consecutive bytes starting at offset k within a lane. -/
def laneBytes : Nat → Bytes → Lane
  | _, [] => 0
  | k, b :: bs => (b.zeroExtend 64 <<< (8*k)) ^^^ laneBytes (k+1) bs

private theorem feedWithin (a : State) (lane k : Nat) (input : Bytes)
    (valid : lane < a.size) (bounded : k+input.length≤8) (within : 8*lane+k+input.length<136) :
    input.foldl feed (a,8*lane+k) =
      (a.setIfInBounds lane (a[lane]! ^^^ laneBytes k input),8*lane+k+input.length) := by
  induction input generalizing a k with
  | nil =>
    simp only [List.foldl_nil,List.length_nil,Nat.add_zero,laneBytes,BitVec.xor_zero]
    congr 1
    apply Array.ext <;> simp_all [Array.getElem_setIfInBounds,getElem!_pos]
  | cons b bs ih =>
    simp only [List.length_cons] at bounded within ⊢
    have bytePos : k<8 := by omega
    have idx : (8*lane+k)/8=lane := by omega
    have offset : (8*lane+k)%8=k := by omega
    simp only [List.foldl_cons,feed,xorByte,idx,offset,if_neg (by omega : 8*lane+k+1≠136)]
    rw [show 8*lane+k+1=8*lane+(k+1) by omega,ih _ _ (by simpa) (by omega) (by omega)]
    congr 1
    · apply Array.ext
      · simp
      · intro j hj hj'
        by_cases same : lane=j
        · subst j
          simp (disch := simp_all) [Array.getElem_setIfInBounds,getElem!_pos,valid,laneBytes,BitVec.xor_assoc]
        · simp (disch := simp_all) [Array.getElem_setIfInBounds,valid,same,Ne.symm same]
    · omega

private theorem laneBytes_append (k : Nat) (xs ys : Bytes) :
    laneBytes k (xs++ys) = laneBytes k xs ^^^ laneBytes (k+xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [laneBytes]
  | cons b xs ih => simp [laneBytes,ih,BitVec.xor_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Absorbing one aligned word is equivalent to eight FIPS 202 byte steps,
including the permutation when this word completes the rate block. -/
theorem feedWord (a : State) (lane : Nat) (input : Bytes) (eight : input.length=8)
    (valid : lane<a.size) (rate : lane<17) :
    input.foldl feed (a,8*lane) =
      let next := a.setIfInBounds lane (a[lane]! ^^^ laneBytes 0 input)
      if lane=16 then (permute next,0) else (next,8*lane+8) := by
  by_cases last : lane=16
  · subst lane
    obtain ⟨initBytes,b,rfl⟩ : ∃ l b, input=l++[b] := by
      induction input using List.reverseRecOn with
      | nil => simp at eight
      | append_singleton l b _ => exact ⟨l,b,rfl⟩
    have seven : initBytes.length=7 := by simpa using eight
    rw [List.foldl_append]
    rw [show 8*16=8*16+0 by decide,feedWithin a 16 0 initBytes valid (by omega) (by omega)]
    simp only [seven,List.foldl_cons,List.foldl_nil,feed,xorByte,ite_true]
    simp only [laneBytes_append,seven,laneBytes, Nat.zero_add, BitVec.xor_zero]
    congr 2
    apply Array.ext
    · simp
    · intro j hj hj'
      by_cases eq : j=16
      · subst j; simp (disch := simp_all) [Array.getElem_setIfInBounds,getElem!_pos,BitVec.xor_assoc]
      · simp (disch := simp_all) [Array.getElem_setIfInBounds,eq,Ne.symm eq]
  · simp only [if_neg last]
    simpa [eight] using feedWithin a lane 0 input valid (by omega) (by omega)
end Spec.Keccak
