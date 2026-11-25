import Cachepath.NativeVerify.ActiveHashProgram
import Shakebatch.Header
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.ActiveHash
open ShakeBatch
variable [machine : Machine]
theorem seed_rows (sw : Array U64 4#usize) (s : Matrix machine.width)
    (count : Usize) (room : count.val ≤ 4) :
    header_active_loop0 ⟨0#usize,count⟩ s sw ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if k < count.val then sw.val[k]!.bv else cell s k j ⦄ := by
  unfold header_active_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => count.val-q.1.start.val)
    (inv := fun q => q.1.end=count ∧ q.1.start.val ≤ count.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if k < q.1.start.val then sw.val[k]!.bv else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold header_active_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < count.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step as ⟨w,hw⟩
      step as ⟨st,write⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      by_cases same : k=it.start.val
      · subst k
        have index : it.start.val < state.val.length := by simpa using hk
        rw [if_pos (by omega),cell,write,Array.set_val_eq,setSame _ _ _ index,Array.repeat_val]
        rw [hw,←getElem!_pos]; simp [hj]
      · have equiv : k < nxt.start.val ↔ k < it.start.val := by omega
        rw [if_congr equiv rfl rfl,← h k hk j hj]
        rw [cell,write,Array.set_val_eq,setOther _ _ _ _ (Ne.symm same)]
        rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=count.val := by rw [he] at more; omega
      simpa only [eq] using h
  · simp
theorem address_lane (s : Matrix machine.width) (base lane : Usize) (addr : Array U64 4#usize)
    (fits : base.val+4 ≤ 25) (valid : lane.val < machine.width.val) :
    header_active_loop1_loop0 base ⟨0#usize,4#usize⟩ s lane addr ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if j=lane.val ∧ base.val ≤ k ∧ k < base.val+4 then addr.val[k-base.val]!.bv else cell s k j ⦄ := by
  unfold header_active_loop1_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => 4-q.1.start.val)
    (inv := fun q => q.1.end=4#usize ∧ q.1.start.val ≤ 4 ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if j=lane.val ∧ base.val ≤ k ∧ k < base.val+q.1.start.val then addr.val[k-base.val]!.bv else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold header_active_loop1_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < 4 := by rw [he] at more; exact more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step as ⟨w,hw⟩
      step as ⟨r,index⟩
      step as ⟨a,back,read,write⟩
      step as ⟨a',update⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write,update,read,← getElem!_pos,cell_write _ _ _ _ (by omega) valid,index,h k hk j hj]
      by_cases col : j=lane.val
      · subst j
        by_cases row : k=base.val+it.start.val
        · subst k
          rw [hw,←getElem!_pos];simp [hn]
        · have equiv : k < base.val+nxt.start.val ↔ k < base.val+it.start.val := by omega
          simp [row,equiv]
      · simp [col]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = 4 := by rw [he] at more; scalar_tac
      simpa only [eq] using h
  · simp


/-- Each state receives the exact FIPS address of its own lane, including every high zero byte. -/
theorem address_rows (s : Matrix machine.width) (base : Usize)
    (addresses : Array address.Adrs machine.width) (active : Usize) (boundActive : active.val ≤ machine.width.val) (fits : base.val+4 ≤ 25) :
    header_active_loop1 base ⟨0#usize,active⟩ addresses s ⦃ out =>
      ∀ k < 25, ∀ j < active.val, cell out k j =
        if base.val ≤ k ∧ k < base.val+4 then addressWord addresses.val[j]! (k-base.val) else cell s k j ⦄ := by
  unfold header_active_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => active.val-q.1.start.val)
    (inv := fun q => q.1.end=active ∧ q.1.start.val ≤ active.val ∧
      ∀ k < 25, ∀ j < active.val, cell q.2 k j =
        if j < q.1.start.val ∧ base.val ≤ k ∧ k < base.val+4 then addressWord addresses.val[j]! (k-base.val) else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold header_active_loop1.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < active.val := he ▸ more
      have wide : it.start.val < machine.width.val := lt.trans_le boundActive
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step as ⟨a,get⟩
      step with address_spec a as ⟨addr,full⟩
      step with address_lane state base it.start addr fits wide as ⟨st,write⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write k hk j (hj.trans_le boundActive),h k hk j hj]
      by_cases col : j=it.start.val
      · subst j
        rw [get,← getElem!_pos] at full
        by_cases inRow : base.val ≤ k ∧ k < base.val+4
        · have row := full (k-base.val) (by omega)
          simp [hn,inRow] at row ⊢
          exact row
        · simp [hn,inRow]
      · have equiv : j < nxt.start.val ↔ j < it.start.val := by omega
        simp [col,equiv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=active.val := by rw [he] at more; omega
      intro k hk j hj
      simpa [eq,hj] using h k hk j hj
  · simp

end slhdsa.NativeVerify.ActiveHash
