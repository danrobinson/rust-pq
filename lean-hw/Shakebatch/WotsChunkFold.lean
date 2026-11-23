import Shakebatch.WotsStores
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ShakeBatch
abbrev ChunkIter := core.slice.iter.Chunks Usize
abbrev nextChunk := @core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next Usize

theorem chunk_fold {A : Type} (body : ChunkIter → A → Result (ControlFlow (ChunkIter × A) A))
    (ds : List U32) (order : Slice Usize) (width : Usize) (positive : 0 < width.val)
    (length : order.length=ds.length) (orderOk : BatchMatches ds order 0)
    (P : Nat → A → Prop) (state : A) (init : P 0 state)
    (done : ∀ it s, nextChunk it=ok (none,it) → P ds.length s → body it s=ok (ControlFlow.done s))
    (advance : ∀ offset it next slice s, P offset s → BatchMatches ds slice offset →
      0<slice.length → slice.length≤width.val →
      nextChunk it=ok (some slice,next) → body it s ⦃ r => ∃ newState, r=.cont (next,newState) ∧ P (offset+slice.length) newState ⦄) :
    loop (fun (q : ChunkIter × A) => body q.1 q.2) (⟨order,width⟩,state) ⦃ result => P ds.length result ⦄ := by
  apply loop.spec_decr_nat (measure := fun q : ChunkIter × A => q.1.rest.length)
    (inv := fun q => q.1.width=width ∧ ∃ pos, pos≤ds.length ∧ q.1.rest.val=order.val.drop pos ∧ P pos q.2)
  · rintro ⟨it,s⟩ ⟨stepWidth,pos,valid,rest,prior⟩
    simp only at stepWidth valid rest prior
    have size : it.rest.length=ds.length-pos := by simp [Slice.length,rest,← length]
    by_cases live : pos<ds.length
    · let slice := Slice.from (it.rest.val.take width.val) (by have := it.rest.property;simp <;> omega)
      let tail := Slice.from (it.rest.val.drop width.val) (by have := it.rest.property;simp <;> omega)
      let nxt : ChunkIter := ⟨tail,width⟩
      have active : slice.length=min width.val (ds.length-pos) := by simp only [slice,Slice.length,Slice.from_val,List.length_take];exact congrArg (min width.val) size
      have stop : it.rest.val.isEmpty=false := by simp;intro eq;have h := congrArg List.length eq;change it.rest.length=0 at h;omega
      have ran : nextChunk it=ok (some slice,nxt) := by
        simp only [nextChunk,core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
          stop,Bool.false_eq_true,ite_false,stepWidth,show width.val≠0 by omega]
        rfl
      have rows : BatchMatches ds slice pos := by
        intro j hj
        have bound : pos+j<order.length := by omega
        have h := orderOk (pos+j) bound
        change slice.val[j]!.val < _ ∧ _=_
        have taken : slice.val[j]! = it.rest.val[j]! := by
          simp only [slice,Slice.from_val]
          exact List.getElem!_take_of_lt width.val j it.rest.val (by omega)
        have remBound : j < (order.val.drop pos).length := by
          rw [List.length_drop]; change j < order.length-pos; omega
        have read : (order.val.drop pos)[j]! = order.val[pos+j]! := by
          rw [getElem!_pos (order.val.drop pos) j remBound,List.getElem_drop,← getElem!_pos]
        rw [taken,rest,read]
        simpa using h
      step with advance pos it nxt slice s prior rows (by omega) (by omega) ran as ⟨r,next,hr,progress⟩
      rw [hr]
      refine ⟨rfl,⟨pos+slice.length,by omega,?_,progress⟩,?_⟩
      · simp only [nxt,tail,Slice.from_val,rest,List.drop_drop]
        by_cases full : width.val≤ds.length-pos
        · simp [active,min_eq_left full,Nat.add_comm]
        · have orderLen : order.val.length=ds.length := length
          rw [List.drop_eq_nil_of_le (by omega),List.drop_eq_nil_of_le (by omega)]
      · change tail.length < it.rest.length
        simp only [tail,Slice.length,Slice.from_val,List.length_drop]
        change it.rest.length-width.val < it.rest.length
        omega
    · have eq : pos=ds.length := by omega
      have empty : it.rest.val=[] := List.length_eq_zero_iff.mp (show it.rest.length=0 by omega)
      have ran : nextChunk it=ok (none,it) := by simp [nextChunk,core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,empty]
      rw [done it s ran (eq ▸ prior)]
      simpa only [step_simps] using eq ▸ prior
  · exact ⟨rfl,0,Nat.zero_le _,by simp,init⟩

end slhdsa.ShakeBatch
