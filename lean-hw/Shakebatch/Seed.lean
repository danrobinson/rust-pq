import Shakebatch.Words

open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def cell (s : Matrix machine.width) (k lane : Nat) : BitVec 64 := (s.val[k]!.val[lane]!).bv

def inputWord (input : List U8) (k : Nat) : BitVec 64 :=
  Spec.Keccak.laneBytes 0 (bytes ((input.drop (k*8)).take 8))

omit machine in
theorem setSame {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by simp [hi]

omit machine in
theorem setOther {α} [Inhabited α] (xs : List α) (i k : Nat) (x : α) (hne : i ≠ k) :
    (xs.set i x)[k]! = xs[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]

/-- Copy the complete seed words into every independent permutation state. -/
theorem seed_rows {N : Usize} (seed : Array U8 N) (s : Matrix machine.width)
    (count : Usize) (size : count.val*8 ≤ N.val) (room : count.val ≤ 25) :
    shake.batch.header_loop0 ⟨0#usize,count⟩ seed s ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if k < count.val then inputWord seed.val k else cell s k j ⦄ := by
  unfold shake.batch.header_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => count.val-q.1.start.val)
    (inv := fun q => q.1.end=count ∧ q.1.start.val ≤ count.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if k < q.1.start.val then inputWord seed.val k else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.header_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < count.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step with word_spec (Array.to_slice seed) it.start (by simp; omega) as ⟨w,hw⟩
      step as ⟨st,write⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      by_cases same : k=it.start.val
      · subst k
        have index : it.start.val < state.val.length := by simpa using hk
        rw [if_pos (by omega),cell,write,Array.set_val_eq,setSame _ _ _ index,Array.repeat_val]
        simpa [hj,inputWord,Array.val_to_slice] using hw
      · have equiv : k < nxt.start.val ↔ k < it.start.val := by omega
        rw [if_congr equiv rfl rfl,← h k hk j hj]
        rw [cell,write,Array.set_val_eq,setOther _ _ _ _ (Ne.symm same)]
        rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=count.val := by rw [he] at more; omega
      simpa only [eq] using h
  · simp
end slhdsa.ShakeBatch
