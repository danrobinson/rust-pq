import Leaf256.Address
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256

private theorem payload_link (b : Nat → Word) (ws : List Word) (idx chg : Word) (n k : Nat)
    (shape : n = 16 ∨ n = 24 ∨ n = 32) :
    leafWords b (fun i => ws[i]!) idx chg n k = payloadWord (withType (prfWords b idx) chg) ws n k := by
  by_cases k2 : k = 2
  · subst k; simp (disch := omega) only [leafWords,payloadWord,withType,prfWords,if_pos,if_neg,↓reduceIte]
  by_cases k5 : k = 5
  · subst k
    simp (disch := omega) only [leafWords,payloadWord,withType,prfWords,if_pos,if_neg,↓reduceIte]
    leaf_bits
  by_cases last : k = 5+n/4
  · subst k; simp (disch := omega) only [leafWords,payloadWord,withType,prfWords,if_pos,if_neg,↓reduceIte]
  by_cases mid : 6 ≤ k ∧ k < 5+n/4 <;>
    simp (disch := omega) only [leafWords,payloadWord,withType,if_pos,if_neg,↓reduceIte]

theorem leaf_layout (a : LeafRust.address.Adrs) (sk : Spec.Bytes) (i n : Nat) (ws : List Word)
    (shape : n = 16 ∨ n = 24 ∨ n = 32) (hs : sk.length = n) (hws : ws.length = 8)
    (hi : i < 2^32) :
    blockOf (leafWords (fun k => word (template a sk) (4*k)) (fun k => ws[k]!)
      (BitVec.ofNat 32 i) (typeChange a) n) =
    padFrom 64 ((leafAddress (adrsS (addressOf a)) i).compress ++ (ser ws).take n) := by
  let A := adrsS (addressOf a)
  let old := padFrom 64 ((prfAddress A i).compress ++ sk)
  let typed := leafAddress A i
  have change_eq : typeChange a = ((6#8 ^^^ BitVec.ofNat 8 A.typ).setWidth 32) <<< 16 := by
    unfold typeChange
    simp only [UScalar.hcast_bv_eq,UScalar.bv_xor,cast_u8_bv32]
    change ((BitVec.ofNat 8 a.typ.val ^^^ 6#8).setWidth 32) <<< 16 = _
    rw [BitVec.xor_comm]
    rfl
  have len : ((ser ws).take n).length = n := by simp [ser_length,hws]; omega
  have hp (k : Nat) (hk : k < 16) :
      prfWords (fun t => word (template a sk) (4*t)) (BitVec.ofNat 32 i) k = word old (4*k) := by
    rw [← word_blockOf (prfWords (fun t => word (template a sk) (4*t)) (BitVec.ofNat 32 i)) k hk,prf_layout a sk i (by omega) hi]
  let dest := padFrom 64 (typed.compress ++ (ser ws).take n)
  apply Eq.trans _ (block_words_inverse dest (padFrom_blk_length _ _ (by omega)))
  apply block_congr
  intro k hk
  rw [payload_link _ _ _ _ _ _ shape,change_eq]
  have tag (t : Nat) (h : t < 16) : withType (prfWords (fun u => word (template a sk) (4*u))
        (BitVec.ofNat 32 i)) (((6#8 ^^^ BitVec.ofNat 8 A.typ).setWidth 32) <<< 16) t = word (padFrom 64 (typed.compress ++ sk)) (4*t) := by
    rw [← typed_word A i sk (by omega) t]
    simp (disch := omega) only [withType,hp,old]
  have eq := payload_word typed.compress sk (padTail n) ws n k (adrs_compress_length _) hs hws shape
  unfold dest
  rw [padFrom_blk _ _ (by omega),len]
  rw [← eq]
  simp (disch := omega) only [payloadWord,tag,padFrom_blk _ _ (show sk.length ≤ 33 by omega),hs]

end slhdsa.X86.Leaf
