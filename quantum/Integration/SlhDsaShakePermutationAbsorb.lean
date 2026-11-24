import Integration.SlhDsaShakePermutationCompletion
import Integration.SlhDsaShakePermutationXof

namespace Reduction.ShakePermutation
open Spec.Keccak
private theorem byte_at (b : Spec.Byte) (x y : Fin 8) :
    (((b.zeroExtend 64 <<< (8*x.val)) >>> (8*y.val)).truncate 8) = if x = y then b else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases he : x = y
  · subst y
    simp [BitVec.truncate,BitVec.getLsbD_ushiftRight,hk,show 8*x.val+k < 64 by omega]
  · have ne : x.val ≠ y.val := fun h => he (Fin.ext h)
    simp only [ite_eq_right he,BitVec.truncate,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft,hk,decide_true,Bool.true_and]
    by_cases lo : y.val < x.val
    · simp [show ¬8*x.val ≤ 8*y.val+k by omega]
    · simp [BitVec.getLsbD_of_ge _ _ (show 8 ≤ 8*y.val+k-8*x.val by omega)]

private theorem extract_xor (a : State) (ha : a.size = 25) (pos i : Nat) (hp : pos < 200) (hi : i < 200)
    (b : Spec.Byte) :
    extractByte (xorByte a pos b) i = extractByte a i ^^^ (if pos = i then b else 0) := by
  have pi : pos/8 < a.size := by omega
  have ii : i/8 < a.size := by omega
  by_cases lane : pos/8 = i/8
  · simp only [xorByte,extractByte,getElem!_pos,Array.size_setIfInBounds,pi,ii,Array.getElem_setIfInBounds]
    have h : (⟨pos%8,Nat.mod_lt _ (by decide)⟩ : Fin 8) = ⟨i%8,Nat.mod_lt _ (by decide)⟩ ↔ pos = i := by
      simp [Fin.ext_iff]; omega
    rw [ite_eq_left lane,BitVec.ushiftRight_xor_distrib,BitVec.truncate,BitVec.setWidth_xor]
    have e := byte_at b ⟨pos%8,Nat.mod_lt _ (by decide)⟩ ⟨i%8,Nat.mod_lt _ (by decide)⟩
    change _ ^^^ (((b.zeroExtend 64 <<< (8*(pos%8))) >>> (8*(i%8))).truncate 8) = _
    rw [e,if_congr h rfl rfl]
    simp [lane]
  · have ne : pos ≠ i := fun h => lane (congrArg (· / 8) h)
    simp [xorByte,extractByte,getElem!_pos,pi,ii,lane,ne]


private def mix (a : State) (pos : Nat) : Spec.Bytes → State
  | [] => a
  | b :: bs => mix (xorByte a pos b) (pos+1) bs

private theorem mix_extracted (a : State) (ha : a.size=25) (pos i : Nat) (xs : Spec.Bytes)
    (hi : i < 200) (h : pos + xs.length ≤ 136) :
    extractByte (mix a pos xs) i = extractByte a i ^^^ (if pos ≤ i then xs[i-pos]?.getD 0 else 0) := by
  induction xs generalizing a pos with
  | nil => simp [mix]
  | cons b xs ih =>
    simp only [List.length_cons] at h
    rw [mix,ih _ (by simp [xorByte,ha]) (pos+1) (by omega),extract_xor a ha pos i (by omega) hi b]
    rcases lt_trichotomy pos i with lt|eq|gt
    · rw [ite_eq_right (by omega : pos ≠ i),ite_eq_left (by omega : pos+1 ≤ i),ite_eq_left (by omega : pos ≤ i),
        show i-pos = (i-(pos+1))+1 by omega]
      simp
    · subst i; simp
    · simp [show ¬pos+1 ≤ i by omega,show ¬pos ≤ i by omega,show pos ≠ i by omega]

private theorem fold_block (p : State → State) (a : State) (pos : Nat) (xs : Spec.Bytes)
    (ne : xs ≠ []) (h : pos+xs.length=136) :
    xs.foldl (feed p) (a,pos) = (p (mix a pos xs),0) := by
  induction xs generalizing a pos with
  | nil => contradiction
  | cons b bs ih =>
    simp only [List.length_cons] at h
    cases he : bs with
    | nil => simp [he] at h; simp [feed,mix,h]
    | cons c cs =>
      have lt : 0 < bs.length := by simp [he]
      rw [← he]
      simp only [List.foldl_cons,feed,ite_eq_right (show pos+1 ≠ 136 by omega),mix]
      exact ih _ _ (by simp [he]) (by omega)

private theorem packed_ext (a : State) (w : Words) (h : ∀ i, i < 200 →
    extractByte a i = extractByte (unpack w) i) : pack a = w := by
  funext i
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let j := 8*i.val+k/8
  have e := congrArg (fun b : Spec.Byte => b.getLsbD (k%8)) (h j (by dsimp [j]; omega))
  have div : j/8 = i.val := by dsimp [j]; omega
  have rem : j%8 = k/8 := by dsimp [j]; omega
  simp only [extractByte,div,rem,BitVec.truncate,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,
    Nat.mod_lt k (by decide : 0<8),decide_true,Bool.true_and,show 8*(k/8)+k%8=k by omega] at e
  simpa [pack,unpack,getElem!_pos] using e

def blockBytes (r : Rate) : Spec.Bytes := List.ofFn (blockByte r)

private theorem combined (w : Words) (r : Rate) :
    pack (mix (unpack w) 0 (blockBytes r)) = join (rateXor r (rateOf w)) (capOf w) := by
  apply packed_ext
  intro i hi
  rw [mix_extracted _ (by simp [unpack]) _ _ _ hi (by simp [-List.ofFn_succ,blockBytes])]
  let k : Fin 25 := ⟨i/8,by omega⟩
  let j : Fin 8 := ⟨i%8,Nat.mod_lt _ (by decide)⟩
  have ex (v : Words) : extractByte (unpack v) i = laneByte (v k) j := by
    simp [extractByte,unpack,laneByte,getElem!_pos,k,j,show i/8 < 25 by omega]
  rw [ex,ex,ite_eq_left (Nat.zero_le i),Nat.sub_zero]
  by_cases rate : i < 136
  · have small : k.val < 17 := by dsimp [k]; omega
    have read : (blockBytes r)[i]?.getD 0 = blockByte r ⟨i,rate⟩ := by
      simp only [blockBytes,List.getElem?_ofFn,dite_eq_left rate,Option.getD_some]
    rw [read]
    simp only [join,dite_eq_left small,rateXor,rateOf,blockByte,laneByte,UInt64.toBitVec_xor,
      BitVec.ushiftRight_xor_distrib,BitVec.truncate,BitVec.setWidth_xor]
    exact BitVec.xor_comm _ _
  · have big : ¬k.val < 17 := by dsimp [k]; omega
    have read : (blockBytes r)[i]?.getD 0 = 0 := by
      simp only [blockBytes,List.getElem?_ofFn,dite_eq_right rate,Option.getD_none]
    have q : k.val-17+17 = k.val := by omega
    rw [read]
    simp [join,big,capOf,q]

private theorem fold_blockBytes (π : Permutation) (w : Words) (r : Rate) :
    (blockBytes r).foldl (feed (lanes π)) (unpack w,0) =
      (unpack (π (join (rateXor r (rateOf w)) (capOf w))),0) := by
  rw [fold_block _ _ _ _ (by intro h; have := congrArg List.length h; simp [-List.ofFn_succ,blockBytes] at this) (by simp [-List.ofFn_succ,blockBytes])]
  exact congrArg (fun z => (unpack (π z),0)) (combined w r)


theorem flatten_messageBlocks (xs : Spec.Bytes) :
    ((messageBlocks xs).map blockBytes).flatten = padded xs := by
  let n := xs.length/136+1
  let atByte (i : Fin (136*n)) := (padded xs)[i.val]'(by rw [padded_length]; exact i.isLt)
  have bytes : List.ofFn atByte = padded xs := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,padded_length,n]
    · intros; simp only [List.getElem_ofFn,atByte]
  rw [← bytes,List.ofFn_mul' atByte]
  congr 1
  simp only [messageBlocks,List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  unfold blockBytes
  refine congrArg List.ofFn (funext fun j => ?_)
  rw [blockByte_rateBlock]
  have hj : 136*i.val+j.val < (padded xs).length := by
    rw [padded_length]
    have hi : i.val < xs.length/136+1 := i.isLt
    omega
  simp only [List.getElem?_eq_getElem hj,Option.getD_some,atByte]

private theorem fold_blocks (π : Permutation) (xs : List Rate) (w : Words) :
    (xs.map blockBytes).flatten.foldl (feed (lanes π)) (unpack w,0) =
    (unpack (xs.foldl (fun s x => π (join (rateXor x (rateOf s)) (capOf s))) w),0) := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.flatten_cons,List.foldl_append,List.foldl_cons,fold_blockBytes,ih]

theorem finish_messageBlocks (π : Permutation) (xs : Spec.Bytes) :
    finish (lanes π) (xs.foldl (feed (lanes π)) initial) =
      unpack (Fix.ordinary π (messageBlocks xs)) := by
  have init : initial = (unpack 0,0) := by
    refine Prod.ext ?_ rfl
    apply Array.ext
    · simp [initial,unpack]
    · intros; simp [initial,unpack]
  have e := fold_padded (lanes π) xs
  rw [← flatten_messageBlocks xs,init,fold_blocks] at e
  exact (congrArg Prod.fst e).symm

private theorem squeeze_first (p : State → State) (w : Words) (pos n : ℕ) (h : pos+n ≤ 136) :
    squeeze p (unpack w) pos n =
      List.ofFn (fun i : Fin n => blockByte (rateOf w) ⟨pos+i.val,by omega⟩) := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih =>
    rw [squeeze,List.ofFn_succ]
    simp only [ite_eq_right (show pos ≠ 136 by omega),Fin.val_zero,Nat.add_zero,Fin.val_succ]
    apply congrArg₂ List.cons
    · simp [extractByte,blockByte,unpack,rateOf,laneByte,getElem!_pos,show pos/8 < 25 by omega]
    · rw [ih (pos+1) (by omega)]
      refine congrArg List.ofFn (funext fun i => ?_)
      congr 2; omega

theorem answer_blocks (S : MLink.Sha2Set) (π : Permutation) (xs : List SLHDSA.Byte) :
    answer S (lanes π) xs = ShakeXof.head (output_sizes S).2
      (Completion.bytes (rateOf (Fix.ordinary π (messageBlocks (MLink.sp xs))))) := by
  apply Vector.ext
  intro i hi
  simp only [answer,hash,xof,finish_messageBlocks,squeeze_first _ _ 0 _ (show 0+S.vp.params.m ≤ 136 by simpa only [Nat.zero_add] using (output_sizes S).2),
    MLink.cv,Vector.getElem_mk,List.getElem_toArray,List.getElem_map,List.getElem_ofFn,
    Nat.zero_add,ShakeXof.head,Completion.bytes,Vector.getElem_ofFn]

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.answer_blocks
