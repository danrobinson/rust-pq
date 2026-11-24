import Wots.RecoveryEntry
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

def laneValue (h : Hash) (j : Fin 16) (n : Nat) := (ser (stateWords (laneState h j))).take n

theorem signature_value (N : Usize) (sig : Slice U8) (i : Nat) (h : Hash) (j : Fin 16)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (available : N.val*i+N.val ≤ sig.length)
    (words : ∀ k < N.val/4, h.val[k]! j = word (bytes sig.val) (N.val*i+4*k)) :
    laneValue h j N.val = bytes (element N sig i) := by
  change N.val*i+N.val ≤ sig.val.length at available
  let ws := stateWords (laneState h j)
  let off := N.val*i
  have size : ws.length = 8 := by simp [ws,stateWords,laneState]
  have width : N.val ≤ 32 := by omega
  have len : (bytes (element N sig i)).length = N.val := by simp [element]; omega
  have payload : bytes (element N sig i) = ((bytes sig.val).drop off).take N.val := by
    simp [element,off,bytes,List.map_drop,List.map_take]
  change (ser ws).take N.val = _
  apply List.ext_getElem
  · simp [len,ser_length,size]; omega
  · intro k hk hk'
    have small : k < N.val := len ▸ hk'
    rw [← getElem!_pos ((ser ws).take N.val) k hk,← getElem!_pos (bytes (element N sig i)) k hk',payload,getElem!_take_drop _ _ _ _ small,
      List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt small,← List.getElem!_eq_getElem?_getD,
      Digest.ser_byte _ _ (by omega)]
    rw [← Leaf.lane_lookup h j (k/4) (by omega)]
    unfold Leaf.laneWords
    rw [words (k/4) (by omega)]
    rcases (by omega : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3) with r|r|r|r
    all_goals rw [r]; unfold word; dsimp [off]
    · rw [show N.val*i+4*(k/4) = N.val*i+k by omega]; leaf_bits
    · rw [show N.val*i+4*(k/4)+1 = N.val*i+k by omega]; leaf_bits
    · rw [show N.val*i+4*(k/4)+2 = N.val*i+k by omega]; leaf_bits
    · rw [show N.val*i+4*(k/4)+3 = N.val*i+k by omega]; leaf_bits

def chainAt (P : Spec.Params) (N : Usize) (pk : Spec.Bytes) (a : Spec.Adrs)
    (sig : Slice U8) (digits : Slice U32) (i t : Nat) :=
  let d := digits.val[i]!.val
  Spec.chain P (bytes (element N sig i)) d (t-d) pk {a with word2 := i}

/-- In a newly filled lane the truncated SHA state is the length-zero FIPS chain,
regardless of the unused high digest words. -/
theorem loaded_chain (P : Spec.Params) (N : Usize) (pk : Spec.Bytes) (a : Spec.Adrs)
    (sig : Slice U8) (digits : Slice U32) (i : Nat) (h : Hash) (j : Fin 16)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (available : N.val*digits.length ≤ sig.length)
    (bound : i < digits.length) (words : ∀ k < N.val/4, h.val[k]! j = word (bytes sig.val) (N.val*i+4*k)) :
    laneValue h j N.val = chainAt P N pk a sig digits i digits.val[i]!.val := by
  have room := Nat.mul_le_mul_left N.val bound
  rw [Nat.mul_succ] at room
  rw [signature_value N sig i h j shape (by omega) words]
  simp [chainAt,Spec.chain]

/-- A live lane with a partially recovered FIPS chain advances that same chain by
one step. Each lane may have a different signature index and starting digit. -/
theorem advance_chain (P : Spec.Params) [Fact (P.family = .sha2)] (N : Usize) (pk : Spec.Bytes)
    (a : Spec.Adrs) (sig : Slice U8) (digits : Slice U32) (iv pre h : Hash) (w : Words) (counter : Reg)
    (width : N.val = P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length = P.n)
    (seed : ∀ j, stateWords (laneState iv j) = seedState P.n pk)
    (prefixOK : Trace pre (fun j => schedule (recoveryBlock N w h counter j)) (laneState iv) 4) :
    compressRound N iv pre h w counter (fun _ => 0xffff) ⦃ _ out =>
      ∀ j i, let t := (counter j).toNat
      digits.val[i]!.val ≤ t → t < 15 →
      laneValue h j N.val = chainAt P N pk a sig digits i t →
      (∀ g u k, k < 16 → packedWord (chainWords w j) g P.n u k =
        packedWord (fun l => word (template {a with word2 := i} (List.replicate P.n 0)) (4*l)) g P.n u k) →
      laneValue out j N.val = chainAt P N pk a sig digits i (t+1) ⦄ := by
  apply WP.spec_mono (recovery_f_spec P N pk iv pre h w counter width shape hpk seed prefixOK)
  rintro ⟨_,out⟩ result j i
  dsimp only
  intro lo hi value ready
  have hashed := result j {a with word2 := i} (List.replicate P.n 0) (by simp) hi ready
  change laneValue out j P.n = Spec.F _ _ _ (laneValue h j P.n) at hashed
  rw [← width,value] at hashed
  rw [chainAt,show (counter j).toNat+1-digits.val[i]!.val = (counter j).toNat-digits.val[i]!.val+1 by omega,
    chain_succ,show digits.val[i]!.val+((counter j).toNat-digits.val[i]!.val) = (counter j).toNat by omega]
  exact hashed

end slhdsa.X86.Wots
