import Shakebatch.Put
import Slhdsa.Proofs.ShakeAddress
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
instance addressDefault : Inhabited address.Adrs := ⟨⟨default,default,default,default,default,default⟩⟩

/-- Copy the four address words of a single lane. -/
theorem address_lane (s : Matrix machine.width) (base lane : Usize) (addr : Array U8 32#usize)
    (fits : base.val+4 ≤ 25) (valid : lane.val < machine.width.val) :
    shake.batch.header_loop1_loop0 base ⟨0#usize,4#usize⟩ s lane addr ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if j=lane.val ∧ base.val ≤ k ∧ k < base.val+4 then inputWord addr.val (k-base.val) else cell s k j ⦄ := by
  unfold shake.batch.header_loop1_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => 4-q.1.start.val)
    (inv := fun q => q.1.end=4#usize ∧ q.1.start.val ≤ 4 ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if j=lane.val ∧ base.val ≤ k ∧ k < base.val+q.1.start.val then inputWord addr.val (k-base.val) else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.header_loop1_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < 4 := by rw [he] at more; exact more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step with word_spec (Array.to_slice addr) it.start (by simp; omega) as ⟨w,hw⟩
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
          simpa [hn,inputWord,Array.val_to_slice] using hw
        · have equiv : k < base.val+nxt.start.val ↔ k < base.val+it.start.val := by omega
          simp [row,equiv]
      · simp [col]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = 4 := by rw [he] at more; scalar_tac
      simpa only [eq] using h
  · simp
def addressWord (a : address.Adrs) (k : Nat) : BitVec 64 :=
  Spec.Keccak.laneBytes 0 (((adrsS a).bytes.drop (k*8)).take 8)

/-- Each state receives the exact FIPS address of its own lane, including every high zero byte. -/
theorem address_rows (s : Matrix machine.width) (base : Usize)
    (addresses : Array address.Adrs machine.width) (fits : base.val+4 ≤ 25) :
    shake.batch.header_loop1 base ⟨0#usize,machine.width⟩ addresses s ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if base.val ≤ k ∧ k < base.val+4 then addressWord addresses.val[j]! (k-base.val) else cell s k j ⦄ := by
  unfold shake.batch.header_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => machine.width.val-q.1.start.val)
    (inv := fun q => q.1.end=machine.width ∧ q.1.start.val ≤ machine.width.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if j < q.1.start.val ∧ base.val ≤ k ∧ k < base.val+4 then addressWord addresses.val[j]! (k-base.val) else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.header_loop1.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < machine.width.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step as ⟨a,get⟩
      step with adrs_full_spec a as ⟨addr,full⟩
      step with address_lane state base it.start addr fits lt as ⟨st,write⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write k hk j hj,h k hk j hj]
      by_cases col : j=it.start.val
      · subst j
        rw [get,← getElem!_pos] at full
        simp [hn,inputWord,addressWord,full]
      · have equiv : j < nxt.start.val ↔ j < it.start.val := by omega
        simp [col,equiv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=machine.width.val := by rw [he] at more; omega
      intro k hk j hj
      simpa [eq,hj] using h k hk j hj
  · simp

end slhdsa.ShakeBatch
