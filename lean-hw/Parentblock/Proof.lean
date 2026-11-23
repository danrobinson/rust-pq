import Parentblock.Funs
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent

def addressOf (a : ParentBlockRust.address.Adrs) : address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

private theorem address_eq (a : ParentBlockRust.address.Adrs) :
    ParentBlockRust.address.Adrs.compress a = address.Adrs.compress (addressOf a) := rfl

private theorem writeTail {α} (head part : List α) (i count : Nat) (x : α) (hi : i = head.length)
    (h : part.length ≤ count) : (head ++ List.replicate count x).setSlice! i part =
      head ++ part ++ List.replicate (count-part.length) x := by
  have h' : List.replicate count x = List.replicate part.length x ++ List.replicate (count-part.length) x := by
    rw [← List.replicate_add, Nat.add_sub_of_le h]
  rw [h',← List.append_assoc]
  exact setSlice!_mid _ _ _ _ _ hi (by simp)

set_option maxHeartbeats 800000 in
theorem parent_block_spec (N : Usize) (a : ParentBlockRust.address.Adrs) (left right : Slice U8)
    (hn : N.val = 24 ∨ N.val = 32) (hl : left.length = N.val) (hr : right.length = N.val) :
    ParentBlockRust.sha512.parents.parent_block N (Array.repeat 128#usize 0#u8) a left right ⦃ b =>
      bytes b.val = S512.padFrom 128 ((adrsS (addressOf a)).compress ++ bytes left.val ++ bytes right.val) ⦄ := by
  unfold ParentBlockRust.sha512.parents.parent_block
  simp only [address_eq]
  step*
  all_goals try scalar_tac
  have llen : left.val.length = N.val := hl
  have rlen : right.val.length = N.val := hr
  rw [s7_post2,s9_post,s8_post,Array.val_to_slice,block4_post,Array.set_val_eq,s5_post2,s6_post,
    s3_post2,s4_post,s_post2,s2_post,s1_post,Array.val_to_slice,Array.repeat_val,setSlice_rep _ _ _ (by simp)]
  rw [writeTail _ _ _ _ _ (by simp) (by simp [llen]; omega),
    writeTail _ _ _ _ _ (by simp [i_post,llen]) (by simp [llen,rlen]; omega)]
  let head := a.val ++ left.val ++ right.val
  have hsize : head.length = 22 + 2*N.val := by simp [head,llen,rlen]; omega
  have rem : (128#usize).val-a.val.length-left.val.length-right.val.length = (97-2*N.val+8)+1 := by
    simp [llen,rlen]; omega
  rw [rem,List.replicate_succ,set_mid _ _ _ _ _ (by simp [i3_post,i1_post,llen,rlen]; omega)]
  have arrange : head ++ 128#u8 :: List.replicate (97-2*N.val+8) 0#u8 =
      (head ++ [128#u8] ++ List.replicate (97-2*N.val) 0#u8) ++ List.replicate 8 0#u8 := by
    simp [List.replicate_add,List.append_assoc]
  rw [arrange,writeTail _ _ _ _ _ (by simp [hsize]; omega) (by simp)]
  have bits : i6.bv = BitVec.ofNat 64 ((150+2*N.val)*8) := by
    apply BitVec.eq_of_toNat_eq
    rw [U64.bv_toNat,i6_post,UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change i5.val < 2^64; omega)]
    simp only [BitVec.toNat_ofNat,i5_post,i4_post,i1_post]; omega
  rw [show a1.val.length = 8 by simp]
  simp only [List.nil_append,bytes_append,bytes_cons,bytes_nil,bytes_replicate,a1_post,bits,head,a_post,
    Nat.sub_self,List.replicate_zero,List.append_nil]
  let msg := (adrsS (addressOf ‹ParentBlockRust.address.Adrs›)).compress ++ bytes left.val ++ bytes right.val
  have ml : msg.length = 22+2*N.val := by simp [msg,bytes,adrs_compress_length,llen,rlen]; omega
  change msg ++ _ ++ _ ++ _ = S512.padFrom 128 msg
  rcases hn with h | h <;>
    simp only [S512.padFrom,ml,h,List.append_assoc] <;> congr 1 <;> decide +kernel

#print axioms parent_block_spec

end slhdsa.PlatformParent
