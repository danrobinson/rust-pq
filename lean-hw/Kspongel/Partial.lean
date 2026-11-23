import Kspongel.Parts
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformShake.Linux
open Keccak (words)
set_option maxHeartbeats 2000000

/-- Complete the current partial rate block before transferring whole blocks. -/
theorem partialBlock (data : Slice U8) (a : Lanes) (pos i : Usize)
    (room : i.val+136-pos.val ≤ data.length) (idx : i.val≤data.length)
    (rate : pos.val<136) (align : pos.val%8=0) :
    KspongeLRust.shake256.Sponge.absorb_loop1 a pos data i ⦃ out =>
      out.2.2.val≤data.length ∧ out.2.1.val=0 ∧
      remaining data out.1 out.2.1 out.2.2 = remaining data a pos i ⦄ := by
  unfold KspongeLRust.shake256.Sponge.absorb_loop1
  apply loop.spec_decr_nat (measure := fun q : Cursor => data.length-q.2.2.val)
    (inv := fun q => q.2.2.val≤data.length ∧ q.2.1.val<136 ∧ q.2.1.val%8=0 ∧
      (q.2.1.val≠0 → q.2.2.val+136-q.2.1.val≤data.length) ∧
      remaining data q.1 q.2.1 q.2.2 = remaining data a pos i)
  · rintro ⟨st,p,k⟩ ⟨ki,pr,palign,hroom,prior⟩
    simp only at ki pr palign hroom prior ⊢
    unfold KspongeLRust.shake256.Sponge.absorb_loop1.body
    spec_split
    · rename_i nonzero
      have pn : p.val ≠ 0 := by scalar_tac
      have room : k.val+8≤data.length := by specialize hroom pn; omega
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
      by_cases full : p'=KspongeLRust.shake256.RATE
      · have num : p'.val=136 := by simp [full,KspongeLRust.shake256.RATE]
        have last : l.val=16 := by omega
        simp only [full,ite_true]
        rw [permuteEq]
        step with scalar_permute as ⟨out,perm⟩
        refine ⟨by omega,by decide,by decide,fun h => False.elim (h rfl),?_,by omega⟩
        simpa [remaining,perm,last,updated,block] using prior
      · have num : p'.val≠136 := fun h => full (UScalar.eq_of_val_eq (by simpa [KspongeLRust.shake256.RATE] using h))
        have last : l.val≠16 := by omega
        simp only [if_neg full,step_simps]
        refine ⟨by omega,by omega,by omega,fun _ => by specialize hroom pn; omega,?_,by omega⟩
        simpa only [if_neg last,start,← pv,remaining] using prior
    · rename_i stop
      simp only [step_simps]
      exact ⟨ki,by scalar_tac,prior⟩
  · exact ⟨idx,rate,align,fun _ => room,rfl⟩
end slhdsa.PlatformShake.Linux
