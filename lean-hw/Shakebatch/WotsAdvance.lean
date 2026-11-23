import Shakebatch.WotsChainProgram
import Shakebatch.Put
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem copy_lane (count offset lane : Usize) (input output : Matrix machine.width)
    (fits : offset.val+count.val ≤ 25) (valid : lane.val < machine.width.val) :
    shake.batch.chains_loop0_loop1_loop0 ⟨0#usize,count⟩ input offset output lane ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if j=lane.val ∧ offset.val ≤ k ∧ k < offset.val+count.val then cell output (k-offset.val) j else cell input k j ⦄ := by
  unfold shake.batch.chains_loop0_loop1_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => count.val-q.1.start.val)
    (inv := fun q => q.1.end=count ∧ q.1.start.val ≤ count.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if j=lane.val ∧ offset.val ≤ k ∧ k < offset.val+q.1.start.val then cell output (k-offset.val) j else cell input k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.chains_loop0_loop1_loop0.body
    by_cases more : it.start.val < it.end.val
    · have remaining : it.start.val < count.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok]
      step as ⟨row,readRow⟩
      step as ⟨word,readWord⟩
      step as ⟨dest,destAt⟩
      step as ⟨r,back,read,write⟩
      step as ⟨r',update⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write,update,read,← getElem!_pos,cell_write _ _ _ _ (by omega) valid,destAt,h k hk j hj]
      by_cases atCell : k=offset.val+it.start.val ∧ j=lane.val
      · obtain ⟨rfl,rfl⟩ := atCell
        rw [readWord,← getElem!_pos,readRow,← getElem!_pos]
        simp [cell,hn]
      · rw [if_neg atCell]
        have same : (j=lane.val ∧ offset.val ≤ k ∧ k < offset.val+nxt.start.val) ↔
            (j=lane.val ∧ offset.val ≤ k ∧ k < offset.val+it.start.val) := by omega
        simp only [same]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=count.val := by rw [he] at more; omega
      intro k hk j hj
      simpa only [eq] using h k hk j hj
  · simp

theorem advance_lanes (count offset : Usize) (input output : Matrix machine.width)
    (index last : Array U32 machine.width) (fits : offset.val+count.val ≤ 25) :
    shake.batch.chains_loop0_loop1 count ⟨0#usize,machine.width⟩ index last input offset output ⦃ ix out =>
      (∀ j < machine.width.val, ix.val[j]!.val=index.val[j]!.val+
        (if index.val[j]!.val < last.val[j]!.val then 1 else 0)) ∧
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if index.val[j]!.val < last.val[j]!.val ∧ offset.val ≤ k ∧ k < offset.val+count.val
        then cell output (k-offset.val) j else cell input k j ⦄ := by
  let active := fun j : Nat => index.val[j]!.val < last.val[j]!.val
  let progresses := fun (atLane : Nat) (ix : Array U32 machine.width) => ∀ j < machine.width.val,
    ix.val[j]!.val = index.val[j]!.val + (if j<atLane ∧ active j then 1 else 0)
  let copied := fun (atLane : Nat) (st : Matrix machine.width) => ∀ k < 25, ∀ j < machine.width.val,
    cell st k j = if j<atLane ∧ active j ∧ offset.val ≤ k ∧ k<offset.val+count.val
      then cell output (k-offset.val) j else cell input k j
  unfold shake.batch.chains_loop0_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array U32 machine.width × Matrix machine.width => machine.width.val-q.1.start.val)
    (inv := fun q => q.1.end=machine.width ∧ q.1.start.val ≤ machine.width.val ∧ progresses q.1.start.val q.2.1 ∧ copied q.1.start.val q.2.2)
  · rintro ⟨it,ix,st⟩ ⟨he,hi,hix,hst⟩
    simp only at he hi hix hst
    unfold shake.batch.chains_loop0_loop1.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < machine.width.val := he ▸ more
      have old := hix it.start.val lt
      simp only [lt_self_iff_false,false_and,ite_false,Nat.add_zero] at old
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok]
      step as ⟨current,read⟩
      step as ⟨stop,ends⟩
      rw [← getElem!_pos] at read ends
      by_cases live : current < stop
      · have advancing : active it.start.val := by
          unfold active
          rw [← old,← read,← ends]
          exact live
        simp only [live,ite_true]
        step with copy_lane count offset it.start st output fits lt as ⟨st',cells⟩
        step as ⟨v,get⟩
        rw [← getElem!_pos] at get
        have below : v.val < stop.val := by rw [get,← read]; exact live
        have top := stop.hmax
        step as ⟨v',inc⟩ <;> try scalar_tac
        step as ⟨ix',updated⟩
        refine ⟨hen.trans he,by omega,?_,?_,by omega⟩
        · intro j hj
          rw [updated,Array.set_val_eq]
          by_cases here : j=it.start.val
          · subst j
            rw [setSame _ _ _ (by simpa using lt),inc,get,old]
            simp [hn,advancing]
          · rw [setOther _ _ _ _ (Ne.symm here),hix j hj]
            have same : j < nxt.start.val ↔ j < it.start.val := by omega
            simp only [same]
        · intro k hk j hj
          rw [cells k hk j hj,hst k hk j hj]
          by_cases here : j=it.start.val
          · subst j; simp [hn,advancing]
          · have same : j < nxt.start.val ↔ j < it.start.val := by omega
            simp [here,same]
      · have idle : ¬ active it.start.val := by
          unfold active
          rw [← old,← read,← ends]
          exact live
        simp only [live,ite_false,step_simps]
        refine ⟨hen.trans he,by omega,?_,?_,by omega⟩
        · intro j hj; rw [hix j hj]
          by_cases here : j=it.start.val
          · subst j; simp [idle]
          · have same : j < nxt.start.val ↔ j < it.start.val := by omega
            simp only [same]
        · intro k hk j hj; rw [hst k hk j hj]
          by_cases here : j=it.start.val
          · subst j; simp [idle]
          · have same : j < nxt.start.val ↔ j < it.start.val := by omega
            simp only [same]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=machine.width.val := by rw [he] at more; omega
      exact ⟨fun j hj => by simpa [eq,hj,active] using hix j hj,
        fun k hk j hj => by simpa [eq,hj,active] using hst k hk j hj⟩
  · simp [progresses,copied]

end slhdsa.ShakeBatch
