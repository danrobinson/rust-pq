import Shakebatch.Seed
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem cell_write (s : Matrix machine.width) (r lane : Usize) (w : U64)
    (hr : r.val < 25) (hl : lane.val < machine.width.val) (k j : Nat) :
    cell (s.set r (s.val[r.val]!.set lane w)) k j =
      if k=r.val ∧ j=lane.val then w.bv else cell s k j := by
  by_cases row : k=r.val
  · subst k
    have hr' : r.val < s.val.length := by simpa using hr
    unfold cell
    rw [Array.set_val_eq,setSame s.val r.val _ hr',Array.set_val_eq]
    simp only [true_and]
    by_cases col : j=lane.val
    · subst j
      rw [setSame s.val[r.val]!.val lane.val _ (by simpa using hl)]
      simp
    · rw [setOther _ _ _ _ (Ne.symm col)]
      simp [col]
  · simp only [cell,Array.set_val_eq,setOther _ _ _ _ (Ne.symm row),row,false_and,ite_false]

theorem put_row {N : Usize} (s : Matrix machine.width) (offset i : Usize)
    (values : Array (Array U8 N) machine.width)
    (row : offset.val+i.val < 25) (bytesFit : i.val*8+8 ≤ N.val) :
    shake.batch.put_loop0_loop0 ⟨0#usize,machine.width⟩ s offset values i ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if k=offset.val+i.val then inputWord values.val[j]!.val i.val else cell s k j ⦄ := by
  unfold shake.batch.put_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => machine.width.val-q.1.start.val)
    (inv := fun q => q.1.end=machine.width ∧ q.1.start.val ≤ machine.width.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if k=offset.val+i.val ∧ j < q.1.start.val then inputWord values.val[j]!.val i.val else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.put_loop0_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < machine.width.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step as ⟨val,get⟩
      step with word_spec (Array.to_slice val) i (by simpa using bytesFit) as ⟨w,hw⟩
      step as ⟨r,index⟩
      step as ⟨a,back,read,write⟩
      step as ⟨a',update⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write,update,read,← getElem!_pos,cell_write _ _ _ _ (by omega) lt,index,h k hk j hj]
      by_cases pos : k=offset.val+i.val
      · subst k
        by_cases col : j=it.start.val
        · subst j
          simp only [true_and,ite_true,hn,Nat.lt_add_one,ite_false,lt_self_iff_false]
          rw [get,← getElem!_pos] at hw
          simpa only [Array.val_to_slice,inputWord] using hw
        · have equiv : j < nxt.start.val ↔ j < it.start.val := by omega
          simp [col,equiv]
      · simp [pos]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=machine.width.val := by rw [he] at more; omega
      intro k hk j hj
      simpa [eq,hj] using h k hk j hj
  · simp

/-- Insert every payload word at its designated offset without disturbing other state words. -/
theorem put_spec {N : Usize} (s : Matrix machine.width) (offset : Usize)
    (values : Array (Array U8 N) machine.width) (fits : offset.val+N.val/8 ≤ 25) :
    shake.batch.put s offset values ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if offset.val ≤ k ∧ k < offset.val+N.val/8 then inputWord values.val[j]!.val (k-offset.val) else cell s k j ⦄ := by
  unfold shake.batch.put
  step as ⟨last,count⟩
  unfold shake.batch.put_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => last.val-q.1.start.val)
    (inv := fun q => q.1.end=last ∧ q.1.start.val ≤ last.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if offset.val ≤ k ∧ k < offset.val+q.1.start.val then inputWord values.val[j]!.val (k-offset.val) else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.put_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < last.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with put_row state offset it.start values (by omega) (by omega) as ⟨st,write⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write k hk j hj,h k hk j hj]
      by_cases row : k=offset.val+it.start.val
      · subst k
        simp [hn]
      · have equiv : k < offset.val+nxt.start.val ↔ k < offset.val+it.start.val := by omega
        simp only [row,ite_false,equiv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = N.val/8 := by rw [he] at more; omega
      simpa only [eq] using h
  · simp

end slhdsa.ShakeBatch
