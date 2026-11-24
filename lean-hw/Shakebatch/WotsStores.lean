import Shakebatch.WotsBatchIds
import Shakebatch.WotsWords
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 700000
variable [machine : Machine]

def BatchMatches (ds : List U32) (batch : Slice Usize) (offset : Nat) :=
  ∀ j < batch.length, batch.val[j]!.val < ds.length ∧ WotsOrder.rank ds batch.val[j]!.val=offset+j

def SignedPrefix (ds : List U32) (n : Nat) (root : Nat → Spec.Bytes) (processed : Nat) (sig : alloc.vec.Vec U8) :=
  sig.length=ds.length*n ∧ ∀ k < ds.length, WotsOrder.rank ds k<processed →
    ∀ b < n, sig.val[k*n+b]!.bv=(root k)[b]!

def EndpointPrefix {N : Usize} (ds : List U32) (root : Nat → Spec.Bytes) (processed : Nat)
    (endpoints : Array (Array U8 N) 67#usize) :=
  ∀ k < ds.length, WotsOrder.rank ds k<processed → bytes endpoints.val[k]!.val=root k

theorem store_endpoints {N : Usize} (ds : List U32) (root : Nat → Spec.Bytes)
    (offset : Nat) (batch : Slice Usize) (count : ds.length≤67)
    (width : batch.length≤machine.width.val) (ids : BatchMatches ds batch offset)
    (values : Array (Array U8 N) machine.width)
    (correct : ∀ j < batch.length, bytes values.val[j]!.val=root batch.val[j]!.val)
    (out : Array (Array U8 N) 67#usize) (prior : EndpointPrefix ds root offset out) :
    shake.batch.recover_loop0_loop0 ⟨⟨batch,0⟩,0#usize⟩ out values ⦃ result =>
      EndpointPrefix ds root (offset+batch.length) result ⦄ := by
  unfold shake.batch.recover_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Usize) × Array (Array U8 N) 67#usize => batch.length-q.1.iter.i)
    (inv := fun q => q.1.iter.slice=batch ∧ q.1.iter.i≤batch.length ∧ q.1.count.val=q.1.iter.i ∧
      EndpointPrefix ds root (offset+q.1.iter.i) q.2)
  · rintro ⟨⟨⟨s,i⟩,clock⟩,st⟩ ⟨rfl,within,now,old⟩
    simp only at within now old
    unfold shake.batch.recover_loop0_loop0.body core.iter.adapters.enumerate.IteratorEnumerate.next
    simp only [core.iter.traits.iterator.IteratorSliceIter,core.slice.iter.IteratorSliceIter.next]
    by_cases more : i<s.length
    · have live : i<s.len.val := by simpa using more
      have max := s.property
      simp only [dif_pos live,bind_ok,lift]
      step as ⟨next,bump⟩
      have read : s[i]=s.val[i]! := (getElem!_pos s.val i more).symm
      obtain ⟨valid,atRank⟩ := ids i more
      change WotsOrder.rank ds s.val[i]!.val=offset+i at atRank
      rw [read]
      step as ⟨v,get⟩
      step as ⟨result,update⟩
      refine ⟨by omega,by omega,?_,by omega⟩
      intro k hk processed
      change WotsOrder.rank ds k < offset+(i+1) at processed
      rw [update,Array.set_val_eq]
      by_cases here : s.val[i]!.val=k
      · subst k
        rw [setSame _ _ _ (by simpa using valid.trans_le count),get,← getElem!_pos,now]
        exact correct i more
      · rw [setOther _ _ _ _ here]
        apply old k hk
        by_contra! later
        have sameRank : WotsOrder.rank ds k=WotsOrder.rank ds s.val[i]!.val := by omega
        exact here (WotsOrder.rank_injective ds valid hk sameRank.symm)
    · have live : ¬ i<s.len.val := by simpa using more
      simp only [dif_neg live,step_simps]
      simpa only [show i=s.length by omega] using old
  · exact ⟨rfl,Nat.zero_le _,rfl,by simpa using prior⟩

theorem store_signatures {N : Usize} (ds : List U32) (root : Nat → Spec.Bytes)
    (offset : Nat) (batch : Slice Usize) (count : ds.length≤67) (small : N.val≤32)
    (width : batch.length≤machine.width.val) (ids : BatchMatches ds batch offset)
    (values : Array (Array U8 N) machine.width)
    (correct : ∀ j < batch.length, bytes values.val[j]!.val=root batch.val[j]!.val)
    (out : alloc.vec.Vec U8) (prior : SignedPrefix ds N.val root offset out) :
    shake.batch.sign_loop0_loop0 ⟨⟨batch,0⟩,0#usize⟩ out values ⦃ result =>
      SignedPrefix ds N.val root (offset+batch.length) result ⦄ := by
  unfold shake.batch.sign_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Usize) × alloc.vec.Vec U8 => batch.length-q.1.iter.i)
    (inv := fun q => q.1.iter.slice=batch ∧ q.1.iter.i≤batch.length ∧ q.1.count.val=q.1.iter.i ∧
      SignedPrefix ds N.val root (offset+q.1.iter.i) q.2)
  · rintro ⟨⟨⟨s,i⟩,clock⟩,st⟩ ⟨rfl,within,now,old⟩
    simp only at within now old
    unfold shake.batch.sign_loop0_loop0.body core.iter.adapters.enumerate.IteratorEnumerate.next
    simp only [core.iter.traits.iterator.IteratorSliceIter,core.slice.iter.IteratorSliceIter.next]
    by_cases more : i<s.length
    · have live : i<s.len.val := by simpa using more
      have max := s.property
      simp only [dif_pos live,bind_ok,lift]
      step as ⟨next,bump⟩
      have read : s[i]=s.val[i]! := (getElem!_pos s.val i more).symm
      obtain ⟨valid,atRank⟩ := ids i more
      change WotsOrder.rank ds s.val[i]!.val=offset+i at atRank
      rw [read]
      let id := s.val[i]!.val
      have fits : (id+1)*N.val ≤ st.length := by rw [old.1];exact Nat.mul_le_mul_right _ valid
      have cap : ds.length*N.val≤67*32 := Nat.mul_le_mul count small
      step as ⟨pos,pv⟩ <;> try scalar_tac
      step as ⟨id',iv⟩
      step as ⟨stop,sv⟩ <;> try scalar_tac
      step as ⟨part,back,content,len,backEq⟩
      step as ⟨v,get⟩
      try simp only [lift,bind_ok]
      step as ⟨w,cp⟩
      all_goals try (simp [pv,sv,iv,Nat.add_mul] at *;omega)
      have newBytes : (back w).val=st.val.setSlice! (id*N.val) (values.val[i]!).val := by
        rw [backEq,cp,get,← getElem!_pos,now]
        simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val,Array.val_to_slice,pv,id]
      refine ⟨by omega,by omega,⟨?_,?_⟩,by omega⟩
      · change (back w).val.length=_
        rw [newBytes,List.length_setSlice!,← old.1]
      · intro k hk processed b hb
        change WotsOrder.rank ds k < offset+(i+1) at processed
        rw [newBytes]
        by_cases here : id=k
        · subst k
          have capacity : id*N.val+N.val≤st.val.length := by simpa [Nat.add_mul] using fits
          rw [List.getElem!_setSlice!_middle _ _ _ _ (by simp;omega)]
          have val := correct i more
          rw [← val]
          rw [bytes_getElem! _ _ (by simpa using hb),Nat.add_sub_cancel_left,getElem!_pos (values.val[i]!).val b (by simpa using hb)]
        · have earlier : WotsOrder.rank ds k<offset+i := by
            by_contra! later
            have sameRank : WotsOrder.rank ds k=WotsOrder.rank ds s.val[i]!.val := by omega
            exact here (WotsOrder.rank_injective ds valid hk sameRank.symm)
          by_cases less : k < id
          · have e : (k+1)*N.val ≤ id*N.val := Nat.mul_le_mul_right _ less
            rw [List.getElem!_setSlice!_prefix _ _ _ _ (by rw [Nat.add_mul] at e;omega),old.2 k hk earlier b hb]
          · have e : (id+1)*N.val ≤ k*N.val := Nat.mul_le_mul_right _ (by omega)
            rw [List.getElem!_setSlice!_suffix _ _ _ _ (by simp;rw [Nat.add_mul] at e;omega),old.2 k hk earlier b hb]
    · have live : ¬ i<s.len.val := by simpa using more
      simp only [dif_neg live,step_simps]
      simpa only [show i=s.length by omega] using old
  · exact ⟨rfl,Nat.zero_le _,rfl,by simpa using prior⟩

end slhdsa.ShakeBatch
