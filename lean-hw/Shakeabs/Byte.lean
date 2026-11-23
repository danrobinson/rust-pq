import Shakeabs.Aligned
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake
open Keccak (words)

theorem byte_suffix (data : Slice U8) (st out : Lanes) (p p' k k' : Usize) (lt : k.val<data.length)
    (advance : k'.val=k.val+1)
    (next : (words out,p'.val)=Spec.Keccak.feed (words st,p.val) data.val[k.val]!.bv) :
    remaining data out p' k' = remaining data st p k := by
  unfold remaining
  rw [← List.getElem_cons_drop (show k.val<(bytes data.val).length by simpa using lt),List.foldl_cons]
  simpa [next,advance,bytes,getElem!_pos,lt]

theorem tail (data : Slice U8) (a : Lanes) (pos i : Usize) (idx : i.val≤data.length)
    (rate : pos.val<136) :
    ShakeAbsRust.shake256.Sponge.absorb_loop2 a pos data i ⦃ out =>
      out.2.val<136 ∧ (words out.1,out.2.val)=remaining data a pos i ⦄ := by
  unfold ShakeAbsRust.shake256.Sponge.absorb_loop2
  apply loop.spec_decr_nat (measure := fun q : Cursor => data.length-q.2.2.val)
    (inv := fun q => q.2.2.val≤data.length ∧ q.2.1.val<136 ∧
      remaining data q.1 q.2.1 q.2.2 = remaining data a pos i)
  · rintro ⟨st,p,k⟩ ⟨ki,pr,prior⟩
    simp only at ki pr prior ⊢
    simp only [ShakeAbsRust.shake256.Sponge.absorb_loop2.body,step_simps]
    spec_split
    · rename_i more
      have lt : k.val<data.length := by scalar_tac
      step as ⟨b,read⟩
      simp only [lift,bind_ok]
      step as ⟨offset,rem⟩
      step as ⟨bits,shift⟩
      step as ⟨value,_,bv⟩
      step as ⟨lane,div⟩
      step as ⟨old,word⟩
      step as ⟨_,back,_,write⟩
      step as ⟨p',inc⟩
      let newState := back (old ^^^ value)
      have update : words newState=Spec.Keccak.xorByte (words st) p.val data.val[k.val]!.bv := by
        simp only [newState,write,words_set,Spec.Keccak.xorByte,← div,UScalar.bv_xor,bv,
          shift,rem,word,Keccak.words_get st lane.val (by scalar_tac),UScalar.cast_bv_eq,read,
          getElem!_pos data.val k.val lt]
        rfl
      by_cases full : p'=ShakeAbsRust.shake256.RATE
      · have num : p.val+1=136 := by rw [← inc,full]; simp [ShakeAbsRust.shake256.RATE]
        simp only [full,ite_true,Std.bind_assoc,bind_ok]
        step with scalar_permute as ⟨out,perm⟩
        step as ⟨k',adv⟩
        refine ⟨by omega,by decide,Eq.trans (byte_suffix _ _ _ _ _ _ _ lt adv ?_) prior,by omega⟩
        simp only [Spec.Keccak.feed,num,ite_true,perm,← update]; rfl
      · have num : p.val+1≠136 := fun eq => full (UScalar.eq_of_val_eq (by simpa [ShakeAbsRust.shake256.RATE,inc] using eq))
        simp only [if_neg full,bind_ok]
        step as ⟨k',adv⟩
        refine ⟨by omega,by omega,Eq.trans (byte_suffix _ _ _ _ _ _ _ lt adv ?_) prior,by omega⟩
        simp only [Spec.Keccak.feed,if_neg num,← update,inc]; rfl
    · have endAt : k.val=data.length := by scalar_tac
      simp only [step_simps]
      exact ⟨pr,by simpa [remaining,endAt,List.drop_eq_nil_of_le] using prior⟩
  · exact ⟨idx,rate,rfl⟩
end slhdsa.PlatformShake
