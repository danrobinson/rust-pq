import Wots.Layout
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

def keyWords (w : Nat → Word) (key chain : Word) (k : Nat) :=
  if k = 2 then w 2 ||| (key >>> 16)
  else if k = 3 then key <<< 16
  else if k = 4 then chain <<< 16
  else w k

def keyPacket (head : Spec.Bytes) (key chain : Word) (tail : Spec.Bytes) :=
  head ++ (Spec.toByte key.toNat 4 ++ (Spec.toByte chain.toNat 4 ++ (Spec.toByte 0 4 ++ tail)))

/-- Patching three native words constructs the two big-endian FIPS address fields. -/
theorem key_words_layout (head tail : Spec.Bytes) (key : Word) (chain : BitVec 16)
    (k : Nat) (hh : head.length = 10) :
    keyWords (fun i => word (keyPacket head 0 0 tail) (4*i)) key (chain.setWidth 32) k =
      word (keyPacket head key (chain.setWidth 32) tail) (4*k) := by
  have len (x : Nat) : (Spec.toByte x 4).length = 4 := by simp [Spec.toByte]
  by_cases small : k < 2
  · simp (disch := omega) only [keyWords,keyPacket,if_neg,word,List.getElem!_append_left]
  by_cases large : 4 < k
  · simp (disch := omega) only [keyWords,keyPacket,if_neg,word,List.getElem!_append_right,hh,len]
    simp (disch := (simp [Spec.toByte]; omega)) only [List.getElem!_append_right,len]
  rcases (by omega : k=2 ∨ k=3 ∨ k=4) with rfl|rfl|rfl
  all_goals simp (disch := omega) only [keyWords,keyPacket,↓reduceIte,word,
    Nat.reduceMul,Nat.reduceAdd,List.getElem!_append_left,List.getElem!_append_right,hh,len,Nat.reduceSub]
  all_goals simp only [toByte4,show Spec.toByte 0 4 = [0#8,0#8,0#8,0#8] by rfl,
    List.cons_append,List.nil_append,List.getElem!_cons_zero,List.getElem!_cons_succ]
  all_goals leaf_bits

def keyAddress (a : Spec.Adrs) (key chain : Word) : Spec.Adrs :=
  { a with keypair := key.toNat, word2 := chain.toNat, word3 := 0 }

theorem key_packet (a : Spec.Adrs) (key chain : Word) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    padFrom 64 ((keyAddress a key chain).compress ++ m) =
      keyPacket (a.compress.take 10) key chain (m ++ padTail m.length) := by
  rw [padFrom_blk _ _ hm]
  simp only [compress_eq,keyPacket,keyAddress,toByte4_eq]
  rfl

theorem key_address_layout (a : Spec.Adrs) (m : Spec.Bytes) (key : Word) (chain : BitVec 16)
    (small : m.length ≤ 33) :
    let base := padFrom 64 ((keyAddress a 0 0).compress ++ m)
    Leaf.blockOf (keyWords (fun i => word base (4*i)) key (chain.setWidth 32)) =
      padFrom 64 ((keyAddress a key (chain.setWidth 32)).compress ++ m) := by
  dsimp only
  apply Eq.trans _ (Leaf.block_words_inverse _ (padFrom_blk_length _ _ small))
  apply Leaf.block_congr
  intro i _
  rw [key_packet _ _ _ _ small,key_packet _ _ _ _ small]
  apply key_words_layout
  simp [adrs_compress_length]

/-- With a public-seed state, compression of the patched PRF block yields the exact
secret chain element used by Algorithm 6. -/
theorem key_prf_fips (P : Spec.Params) [Fact (P.family = .sha2)] (pk sk : Spec.Bytes)
    (a : Spec.Adrs) (key : Word) (chain : BitVec 16)
    (width : P.n ≤ 32) (hpk : pk.length = P.n) (hsk : sk.length = P.n) :
    let prf := a.setTypeAndClear Spec.WOTS_PRF
    let base := padFrom 64 ((keyAddress prf 0 0).compress ++ sk)
    (ser (compress (seedState P.n pk) (Leaf.blockOf (keyWords (fun i => word base (4*i))
      key (chain.setWidth 32))))).take P.n =
      Spec.PRF P pk sk { Spec.wotsSkAdrs {a with keypair := key.toNat} with word2 := chain.toNat } := by
  dsimp only
  rw [key_address_layout _ _ _ _ (by omega),PRF_eq]
  change _ = th256 P.n pk (keyAddress (a.setTypeAndClear Spec.WOTS_PRF) key (chain.setWidth 32)) sk
  exact th256_one _ _ hpk (by omega) _ _ (by omega)

end slhdsa.X86.Wots
