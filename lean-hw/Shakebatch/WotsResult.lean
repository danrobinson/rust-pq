import Shakebatch.WotsChainProgram
import Shakebatch.Read
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem result_row {N : Usize} (s : Matrix machine.width) (i offset : Usize)
    (values : Array (Array U8 N) machine.width) (within : offset.val+i.val < 25) (fits : i.val*8+8 ≤ N.val) :
    shake.batch.chains_loop1_loop0 ⟨0#usize,machine.width⟩ s offset values i ⦃ out =>
      ∀ j < machine.width.val, ∀ b < N.val, outputByte out j b =
        if 8*i.val ≤ b ∧ b < 8*i.val+8 then stateByte s j (offset.val+i.val) (b-8*i.val) else outputByte values j b ⦄ := by
  unfold shake.batch.chains_loop1_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array (Array U8 N) machine.width => machine.width.val-q.1.start.val)
    (inv := fun q => q.1.end=machine.width ∧ q.1.start.val ≤ machine.width.val ∧
      ∀ j < machine.width.val, ∀ b < N.val, outputByte q.2 j b =
        if j < q.1.start.val ∧ 8*i.val ≤ b ∧ b < 8*i.val+8 then stateByte s j (offset.val+i.val) (b-8*i.val) else outputByte values j b)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.chains_loop1_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < machine.width.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step as ⟨a,restore,get,save⟩
      step as ⟨pos,pv⟩
      step as ⟨stop,sv⟩
      step as ⟨part,back,pr,plen,write⟩
      step as ⟨source,sourceAt⟩
      step as ⟨row,rowAt⟩
      step as ⟨w,word⟩
      simp only [lift,bind_ok]
      step as ⟨copied,cp⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro j hj b hb
      by_cases same : j=it.start.val
      · subst j
        rw [outputByte,save,Array.set_val_eq,setSame _ _ _ (by simpa using lt)]
        rw [write copied,cp,Array.val_to_slice,word_bytes_write _ _ _ _ (by simp [pv];omega)]
        rw [get,← getElem!_pos,word,← getElem!_pos,rowAt,← getElem!_pos]
        change (if _ then _ else outputByte state it.start.val b) = _
        rw [h _ lt b hb]
        simp [hn,pv,stateByte,sourceAt]
      · rw [outputByte,save,Array.set_val_eq,setOther _ _ _ _ (Ne.symm same)]
        change outputByte state j b = _
        rw [h j hj b hb]
        have equiv : j < nxt.start.val ↔ j < it.start.val := by omega
        simp [equiv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=machine.width.val := by rw [he] at more; omega
      intro j hj b hb
      simpa [eq,hj] using h j hj b hb
  · simp

theorem chain_result {N : Usize} (last offset : Usize) (s : Matrix machine.width)
    (initial : Array (Array U8 N) machine.width) (count : last.val=N.val/8)
    (bound : offset.val+last.val ≤ 25) (align : N.val%8=0) :
    shake.batch.chains_loop1 ⟨0#usize,last⟩ s offset initial ⦃ out => ∀ j < machine.width.val, ∀ b < N.val,
      outputByte out j b = stateByte s j (offset.val+b/8) (b%8) ⦄ := by
  unfold shake.batch.chains_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array (Array U8 N) machine.width => last.val-q.1.start.val)
    (inv := fun q => q.1.end=last ∧ q.1.start.val ≤ last.val ∧
      ∀ j < machine.width.val, ∀ b < 8*q.1.start.val, outputByte q.2 j b = stateByte s j (offset.val+b/8) (b%8))
  · rintro ⟨it,values⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.chains_loop1.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < last.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with result_row s it.start offset values (by omega) (by omega) as ⟨st,write⟩
      refine ⟨hen.trans he,by omega,?_,by omega⟩
      intro j hj b hb
      rw [write j hj b (by omega)]
      by_cases new : 8*it.start.val ≤ b
      · have div : b/8=it.start.val := by omega
        have rem : b%8=b-8*it.start.val := by omega
        simp [new,show b < 8*it.start.val+8 by omega,div,rem]
      · simp only [new,false_and,ite_false]
        exact h j hj b (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = N.val/8 := by rw [he] at more; omega
      intro j hj b hb
      exact h j hj b (by omega)
  · simp

end slhdsa.ShakeBatch
