import Shakeabs.Byte
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake
open Keccak (words)

theorem initialBytes (data : Slice U8) (s : ShakeAbsRust.shake256.Sponge) (i : Usize)
    (idx : i.val≤data.length) (rate : s.pos.val<136) :
    ShakeAbsRust.shake256.Sponge.absorb_loop0 s data i ⦃ out => out.2.2.val≤data.length ∧
      out.2.1.val<136 ∧ (out.2.1.val%8=0 ∨ out.2.2.val=data.length) ∧
      remaining data out.1 out.2.1 out.2.2=remaining data s.lanes s.pos i ⦄ := by
  unfold ShakeAbsRust.shake256.Sponge.absorb_loop0
  apply loop.spec_decr_nat (measure := fun q : ShakeAbsRust.shake256.Sponge × Usize => data.length-q.2.val)
    (inv := fun q => q.2.val≤data.length ∧ q.1.pos.val<136 ∧
      remaining data q.1.lanes q.1.pos q.2=remaining data s.lanes s.pos i)
  · rintro ⟨⟨st,p⟩,k⟩ ⟨ki,pr,prior⟩
    simp only at ki pr prior ⊢
    simp only [ShakeAbsRust.shake256.Sponge.absorb_loop0.body,step_simps]
    step as ⟨offset,rem⟩
    spec_split
    · spec_split
      · rename_i more
        have lt : k.val<data.length := by scalar_tac
        step as ⟨b,read⟩
        simp only [lift,bind_ok]
        step as ⟨bits,shift⟩
        step as ⟨value,_,bv⟩
        step as ⟨lane,div⟩
        step as ⟨old,word⟩
        step as ⟨_,back,_,write⟩
        step as ⟨p',inc⟩
        step as ⟨k',adv⟩
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
          refine ⟨by omega,by decide,Eq.trans (byte_suffix _ _ _ _ _ _ _ lt adv ?_) prior,by omega⟩
          simp only [Spec.Keccak.feed,num,ite_true,perm,← update]; rfl
        · have num : p.val+1≠136 := fun eq => full (UScalar.eq_of_val_eq (by simpa [ShakeAbsRust.shake256.RATE,inc] using eq))
          simp only [if_neg full,bind_ok,step_simps]
          refine ⟨by omega,by omega,Eq.trans (byte_suffix _ _ _ _ _ _ _ lt adv ?_) prior,by omega⟩
          simp only [Spec.Keccak.feed,if_neg num,← update,inc]; rfl
      · simp only [step_simps]; exact ⟨ki,pr,Or.inr (by scalar_tac),prior⟩
    · simp only [step_simps]; exact ⟨ki,pr,Or.inl (by scalar_tac),prior⟩
  · exact ⟨idx,rate,rfl⟩
end slhdsa.PlatformShake
