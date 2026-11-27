import Buffered.SmallWotsStream
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify Spec.Keccak
set_option linter.concreteInstances false
set_option maxHeartbeats 1400000
variable [kernel : Fused.Kernel]
local instance groupMachine : Machine := Fused.machine kernel

private abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

private theorem next_group (it : Iter) (endAt K : Usize) (stop : it.iter.end=endAt) (stepSize : it.step_by=K)
    (pos : 0<K.val) (bound : K.val≤8) (fits : it.iter.start.val+K.val≤endAt.val) (limit : endAt.val≤8) :
    core.iter.adapters.step_by.IteratorStepBy.next (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
    ⦃ o next => o=some it.iter.start ∧ next.iter.start.val=it.iter.start.val+K.val ∧ next.iter.end=endAt ∧ next.step_by=K ⦄ := by
  unfold core.iter.adapters.step_by.IteratorStepBy.next
  step with core.iter.range.IteratorRange.next_Usize_some_spec it.iter (by rw [stop]; omega) as ⟨_,r,item,inc,ends⟩
  simp only [item]
  step with core.iter.adapters.step_by.skipN_Range_Usize_spec r (it.step_by.val-1) (by rw [ends,stop]; omega)
    (by scalar_tac) as ⟨u,advance,last⟩
  simp [advance,inc,stepSize,last,ends,stop]
  omega

theorem groups {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (first : U32) (K n endAt : Usize) (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize)
    (start count : Nat) (positive : 0<K.val) (width : K.val≤8) (total : endAt.val=K.val*count)
    (limit : endAt.val≤8) (size : n.val=N.val/8) (rate : pos.val<17)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active)
    (prior : ∀ l<K.val, (ShakeBatch.lane pk l,8*pos.val)=Fused.streamPrefix p sk seed a first.val l start)
    (tips : ∀ t<count, ∀ l<K.val, Wots.digest N state (K.val*t+l)=Fused.tip p sk seed a first.val l (start+t)) :
    leaves_loop2_loop2 K ⟨⟨0#usize,endAt⟩,K⟩ n pk pos state ⦃ out => out.2.val<17 ∧ ∀ l<K.val,
      (ShakeBatch.lane out.1 l,8*out.2.val)=Fused.streamPrefix p sk seed a first.val l (start+count) ⦄ := by
  unfold leaves_loop2_loop2
  apply loop.spec_decr_nat (measure := fun q : Iter × Matrix 8#usize × Usize => endAt.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end=endAt ∧ q.1.step_by=K ∧ q.2.2.val<17 ∧ ∃ t≤count,
      q.1.iter.start.val=K.val*t ∧ ∀ l<K.val, (ShakeBatch.lane q.2.1 l,8*q.2.2.val)=Fused.streamPrefix p sk seed a first.val l (start+t))
  · rintro ⟨it,acc,atPos⟩ ⟨stop,stride,rate',t,le,offset,streams⟩
    simp only at stop stride rate' offset streams ⊢
    unfold leaves_loop2_loop2.body
    by_cases more : t<count
    · have fits : it.iter.start.val+K.val≤endAt.val := by
        rw [offset,total,←Nat.mul_succ]; exact Nat.mul_le_mul_left _ more
      step with next_group it endAt K stop stride positive width fits limit as ⟨_,next,item,inc,last,stride'⟩
      simp only [item]
      let tip := fun l => Fused.tip p sk seed a first.val l (start+t)
      obtain ⟨raw,dig,words⟩ := digest_words (N:=N) state (by have := hp.le32; omega) (aligned_hash hp)
      have equal (l : Nat) (hl : l<K.val) : bytes raw.val[it.iter.start.val+l]!.val=tip l := by
        rw [dig _ (by change it.iter.start.val+l<8; omega),offset]; exact tips t more l hl
      step with absorb_tip K it.iter.start n acc atPos state rate' (by have := hp.le32;omega) (by omega) perm tip
        (by intro l hl; rw [←equal l hl]; simp [bytes]; have := aligned_hash hp; omega)
        (by intro l hl j hj; rw [←equal l hl,←inputWord_eq,words _ (by change it.iter.start.val+l<8; omega) j (by omega)]) as ⟨out,ptr,hr,absorbed⟩
      refine ⟨last,stride',hr,⟨t+1,more,by rw [inc,offset,Nat.mul_succ],?_⟩,by omega⟩
      intro l hl
      rw [absorbed l hl,streams l hl]
      rw [show start+(t+1)=(start+t)+1 by omega]
      simp [Fused.streamPrefix,List.range_succ,List.foldl_append,List.append_assoc,tip]
    · have done : t=count := by omega
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it
        (by rw [stop,total,offset,done]) as ⟨_,next,item,_⟩
      simp only [item,step_simps]
      exact ⟨rate',done ▸ streams⟩
  · exact ⟨rfl,rfl,rate,0,Nat.zero_le _,by simp,by simpa only [Nat.add_zero] using prior⟩

end slhdsa.Buffered.SmallWots
