import Leaf256.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256

/-- Check a fixed-width wiring identity bit by bit in the Lean kernel. -/
macro "leaf_bits" : tactic =>
  `(tactic| (ext bit h
             interval_cases bit <;> simp [BitVec.getElem_append (n := 24) (m := 8),BitVec.getElem_append (n := 16) (m := 8),
               BitVec.getElem_append (n := 8) (m := 8),BitVec.getElem_setWidth,
               BitVec.getElem_extractLsb',BitVec.getElem_or,BitVec.getElem_and,BitVec.getElem_xor,
               BitVec.getElem_shiftLeft,BitVec.getElem_ushiftRight]))

theorem block_words_inverse (b : Spec.Bytes) (len : b.length = 64) :
    blockOf (fun k => word b (4*k)) = b := by
  apply List.ext_getElem
  · simp [blockOf,len]
  · intro i hi hi'
    have r : i%4 < 4 := by omega
    simp only [blockOf,List.getElem_ofFn,word]
    rw [← getElem!_pos b i hi']
    rcases (by omega : i%4 = 0 ∨ i%4 = 1 ∨ i%4 = 2 ∨ i%4 = 3) with h|h|h|h
    all_goals rw [h]
    · rw [show 4*(i/4) = i by omega]
      bv_decide
    · rw [show 4*(i/4)+1 = i by omega]
      bv_decide
    · rw [show 4*(i/4)+2 = i by omega]
      bv_decide
    · rw [show 4*(i/4)+3 = i by omega]
      bv_decide

def prfAddress (a : Spec.Adrs) (i : Nat) : Spec.Adrs :=
  { a.setTypeAndClear Spec.FORS_PRF with keypair := a.keypair, word3 := i }

def leafAddress (a : Spec.Adrs) (i : Nat) : Spec.Adrs := { a with word2 := 0, word3 := i }

theorem template_eq (a : LeafRust.address.Adrs) (sk : Spec.Bytes) :
    template a sk = padFrom 64 ((prfAddress (adrsS (addressOf a)) 0).compress ++ sk) := rfl

private theorem index_word (head tail : Spec.Bytes) (hlen : head.length = 18) (idx : Word) (k : Nat) :
    prfWords (fun t => word (head ++ (Spec.toByte 0 4 ++ tail)) (4*t)) idx k =
      word (head ++ (Spec.toByte idx.toNat 4 ++ tail)) (4*k) := by
  have hzero : (Spec.toByte 0 4).length = 4 := by simp [Spec.toByte]
  have hidx : (Spec.toByte idx.toNat 4).length = 4 := by simp [Spec.toByte]
  by_cases small : k < 4
  · simp (disch := omega) only [prfWords,if_neg,word,List.getElem!_append_left]
  by_cases big : 5 < k
  · simp (disch := omega) only [prfWords,if_neg,word,List.getElem!_append_right,hlen,hidx,hzero]
  rcases (by omega : k = 4 ∨ k = 5) with rfl|rfl
  all_goals simp (disch := omega) only [prfWords,↓reduceIte,word,List.getElem!_append_left,
    List.getElem!_append_right,hlen,hidx,hzero, Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub]
  all_goals simp only [show Spec.toByte 0 4 = [0#8,0#8,0#8,0#8] by rfl,toByte4,
    show (5=4) = False by decide,↓reduceIte,List.getElem!_cons_zero,List.getElem!_cons_succ]
  all_goals leaf_bits

theorem indexed_pad (a : Spec.Adrs) (i : Nat) (sk : Spec.Bytes) (small : sk.length ≤ 33) :
    padFrom 64 ((prfAddress a i).compress ++ sk) =
      (prfAddress a 0).compress.take 18 ++ (Spec.toByte i 4 ++ (sk ++ padTail sk.length)) := by
  rw [padFrom_blk _ _ small]
  change {prfAddress a 0 with word3 := i}.compress ++ _ = _
  rw [compress_word3,List.append_assoc]

theorem prf_layout (a : LeafRust.address.Adrs) (sk : Spec.Bytes) (i : Nat)
    (hsk : sk.length ≤ 33) (hi : i < 2^32) :
    blockOf (prfWords (fun k => word (template a sk) (4*k)) (BitVec.ofNat 32 i)) =
      padFrom 64 ((prfAddress (adrsS (addressOf a)) i).compress ++ sk) := by
  let A := adrsS (addressOf a)
  let dest := padFrom 64 ((prfAddress A i).compress ++ sk)
  apply Eq.trans _ (block_words_inverse dest (padFrom_blk_length _ _ hsk))
  apply block_congr
  intro k _
  simp only [template_eq,dest,indexed_pad _ _ _ hsk]
  have h := index_word ((prfAddress A 0).compress.take 18) (sk ++ padTail sk.length)
    (by simp [adrs_compress_length]) (BitVec.ofNat 32 i) k
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi] using h

end slhdsa.X86.Leaf
