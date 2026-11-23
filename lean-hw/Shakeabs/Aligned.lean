import Shakeabs.Word
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake
open Keccak (words)
abbrev Lanes := Array U64 25#usize
abbrev Cursor := Lanes × Usize × Usize

def remaining (data : Slice U8) (a : Lanes) (pos i : Usize) :=
  ((bytes data.val).drop i.val).foldl Spec.Keccak.feed (words a,pos.val)

theorem aligned (data : Slice U8) (a : Lanes) (pos i : Usize) (idx : i.val≤data.length)
    (rate : pos.val<136) (align : pos.val%8=0 ∨ i.val=data.length) :
    ShakeAbsRust.shake256.Sponge.absorb_loop1 a pos data i ⦃ out =>
      out.2.2.val≤data.length ∧ out.2.1.val<136 ∧
      remaining data out.1 out.2.1 out.2.2 = remaining data a pos i ⦄ := by
  unfold ShakeAbsRust.shake256.Sponge.absorb_loop1
  apply loop.spec_decr_nat (measure := fun q : Cursor => data.length-q.2.2.val)
    (inv := fun q => q.2.2.val≤data.length ∧ q.2.1.val<136 ∧
      (q.2.1.val%8=0 ∨ q.2.2.val=data.length) ∧
      remaining data q.1 q.2.1 q.2.2 = remaining data a pos i)
  · rintro ⟨st,p,k⟩ ⟨ki,pr,aligned,prior⟩
    simp only at ki pr aligned prior ⊢
    unfold ShakeAbsRust.shake256.Sponge.absorb_loop1.body
    step as ⟨left,avail⟩
    spec_split
    · rename_i enough
      have room : k.val+8≤data.length := by scalar_tac
      have palign : p.val%8=0 := by omega
      step as ⟨k',advance⟩
      step as ⟨s,slice,len⟩
      have eight : s.length=8 := by scalar_tac
      simp only [core.array.TryFromArrayCopySlice.try_from,show s.length=(8#usize).val by simpa using eight,
        _root_.dite_true,core.result.Result.unwrap,bind_ok,lift]
      step as ⟨l,lval⟩
      step as ⟨old,read⟩
      step as ⟨_,back,_,write⟩
      step as ⟨p',pv⟩
      let block := Array.from s.val (show s.val.length=(8#usize).val by exact eight)
      let updated := back (old ^^^ core.num.U64.from_le_bytes block)
      have lane : l.val<17 := by omega
      have start : 8*l.val=p.val := by omega
      have update : words updated = (words st).setIfInBounds l.val
          ((words st)[l.val]! ^^^ Spec.Keccak.laneBytes 0 (bytes s.val)) := by
        simp only [updated,write,words_set,UScalar.bv_xor,loaded,block,Array.from_val,read,
          Keccak.words_get st l.val (by scalar_tac)]
      have parts : (bytes data.val).drop k.val = bytes s.val ++ (bytes data.val).drop k'.val := by
        rw [slice,List.slice,bytes_take,bytes_drop,advance,Nat.add_sub_cancel_left,← List.drop_drop]
        exact (List.take_append_drop _ _).symm
      have feed := Spec.Keccak.feedWord (words st) l.val (bytes s.val) (by simpa using eight)
        (by simp [words]; omega) lane
      dsimp only at feed
      rw [start,← update] at feed
      unfold remaining at prior
      rw [parts,List.foldl_append,feed] at prior
      by_cases full : p'=ShakeAbsRust.shake256.RATE
      · have num : p'.val=136 := by simp [full,ShakeAbsRust.shake256.RATE]
        have last : l.val=16 := by omega
        simp only [full,ite_true]
        step with scalar_permute as ⟨out,perm⟩
        refine ⟨by omega,by decide,Or.inl (by decide),?_,by omega⟩
        simpa [remaining,perm,last,updated,block] using prior
      · have num : p'.val≠136 := fun h => full (UScalar.eq_of_val_eq (by simpa [ShakeAbsRust.shake256.RATE] using h))
        have last : l.val≠16 := by omega
        simp only [if_neg full,step_simps]
        refine ⟨by omega,by omega,Or.inl (by omega),?_,by omega⟩
        simpa only [if_neg last,start,← pv,remaining] using prior
    · simp only [step_simps]
      exact ⟨ki,pr,prior⟩
  · exact ⟨idx,rate,align,rfl⟩
end slhdsa.PlatformShake
