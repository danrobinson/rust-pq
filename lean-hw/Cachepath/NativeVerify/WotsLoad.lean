import Cachepath.NativeVerify.WotsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

abbrev LaneValues (width : Usize) := Array (Array U64 4#usize) width
def laneWord {width : Usize} (s : LaneValues width) (l k : Nat) : BitVec 64 :=
  s.val[l]!.val[k]!.bv

omit machine in
/-- A write changes only its lane and word. Every other slot remains usable by the refill schedule. -/
theorem storeWord {width : Usize} (s : LaneValues width) (l j : Usize) (v : U64)
    (hl : l.val < width.val) (hj : j.val < 4) (x k : Nat) :
    laneWord (s.set l ((s.val[l.val]!).set j v)) x k =
      if x=l.val ∧ k=j.val then v.bv else laneWord s x k := by
  unfold laneWord
  rw [Array.set_val_eq]
  by_cases same : x=l.val
  · subst x
    rw [setSame _ _ _ (by simpa),Array.set_val_eq]
    by_cases pos : k=j.val
    · subst k; rw [setSame _ _ _ (by simpa)]; simp
    · rw [setOther _ _ _ _ (Ne.symm pos)]; simp [pos]
  · rw [setOther _ _ _ _ (Ne.symm same)]; simp [same]

theorem load_lane (s : LaneValues machine.width) (lane n : Usize) (blk : Slice U8)
    (valid : lane.val < machine.width.val) (cap : n.val ≤ 4) (fits : 8*n.val ≤ blk.length) :
    recover_loop1_loop0 ⟨0#usize,n⟩ s lane blk ⦃ out =>
      ∀ l k, laneWord out l k = if l=lane.val ∧ k<n.val then inputWord blk.val k else laneWord s l k ⦄ := by
  unfold recover_loop1_loop0
  apply range_fold (recover_loop1_loop0.body lane blk) n s (fun i out =>
    ∀ l k, laneWord out l k = if l=lane.val ∧ k < i then inputWord blk.val k else laneWord s l k)
  · simp
  · intro it st stop live prev
    unfold recover_loop1_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step with word_spec blk it.start (by omega) as ⟨v,word⟩
    step as ⟨a,back,get,write⟩
    step as ⟨row,upd⟩
    refine ⟨next,back row,rfl,ends.trans stop,idx,?_⟩
    intro l k
    rw [write,upd,get,← getElem!_pos,storeWord _ _ _ _ valid (by omega),prev]
    split
    · rename_i h; obtain ⟨rfl,rfl⟩ := h
      rw [ite_eq_left ⟨rfl,by omega⟩]
      exact word
    · rename_i h
      have eq : (l=lane.val ∧ k < it.start.val) ↔ (l=lane.val ∧ k < next.start.val) := by omega
      rw [if_congr eq rfl rfl]
  · intro it st last stop
    unfold recover_loop1_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem refill_load_lane (s : LaneValues machine.width) (lane n : Usize) (blk : Slice U8)
    (valid : lane.val < machine.width.val) (cap : n.val ≤ 4) (fits : 8*n.val ≤ blk.length) :
    recover_loop2_loop3_loop0 ⟨0#usize,n⟩ s lane blk ⦃ out =>
      ∀ l k, laneWord out l k = if l=lane.val ∧ k<n.val then inputWord blk.val k else laneWord s l k ⦄ := by
  exact load_lane s lane n blk valid cap fits

end slhdsa.NativeVerify.Wots
