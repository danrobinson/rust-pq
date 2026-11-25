import Cachepath.NativeVerify.WotsLoad
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

/-- Swap-removing a completed chain moves the entire unconsumed digest of the last lane. -/
theorem move_digest (s : Matrix machine.width) (src dst n : Usize)
    (lastLane : src.val < machine.width.val) (valid : dst.val<machine.width.val) (cap : n.val≤25) :
    recover_loop2_loop3_loop1 ⟨0#usize,n⟩ src s dst ⦃ out =>
      ∀ k l, cell out k l = if k<n.val ∧ l=dst.val then cell s k src.val else cell s k l ⦄ := by
  unfold recover_loop2_loop3_loop1
  apply range_fold (recover_loop2_loop3_loop1.body src dst) n s (fun i out => ∀ k l, cell out k l =
    if k < i ∧ l=dst.val then cell s k src.val else cell s k l)
  · simp
  · intro it st stop live prev
    unfold recover_loop2_loop3_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨row,r⟩
    step as ⟨w,v⟩
    step as ⟨row',back,r',write⟩
    step as ⟨rowOut,set⟩
    refine ⟨next,back rowOut,rfl,ends.trans stop,idx,?_⟩
    intro k l
    have read : w.bv=cell st it.start.val src.val := by
      rw [v,← getElem!_pos,r,← getElem!_pos]; rfl
    rw [write,set,r',← getElem!_pos,cell_write _ _ _ _ (by omega) valid,read,prev,prev]
    split
    · rename_i h; obtain ⟨rfl,rfl⟩ := h
      simp [idx]
    · rename_i h
      have eq : (k < it.start.val ∧ l=dst.val) ↔ (k < next.start.val ∧ l=dst.val) := by omega
      rw [if_congr eq rfl rfl]
  · intro it st last stop
    unfold recover_loop2_loop3_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

/-- An unfinished chain stores every active digest word for its next round. -/
theorem save_digest (s : Matrix machine.width) (v : LaneValues machine.width) (lane n : Usize)
    (valid : lane.val<machine.width.val) (cap : n.val≤4) :
    recover_loop2_loop3_loop2 ⟨0#usize,n⟩ v s lane ⦃ out =>
      ∀ l k, laneWord out l k = if l=lane.val ∧ k<n.val then cell s k l else laneWord v l k ⦄ := by
  unfold recover_loop2_loop3_loop2
  apply range_fold (recover_loop2_loop3_loop2.body s lane) n v (fun i out => ∀ l k, laneWord out l k =
    if l=lane.val ∧ k < i then cell s k l else laneWord v l k)
  · simp
  · intro it st stop live prev
    unfold recover_loop2_loop3_loop2.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨row,r⟩
    step as ⟨w,vv⟩
    step as ⟨old,back,get,write⟩
    step as ⟨out,set⟩
    refine ⟨next,back out,rfl,ends.trans stop,idx,?_⟩
    intro l k
    have read : w.bv=cell s it.start.val lane.val := by rw [vv,← getElem!_pos,r,← getElem!_pos]; rfl
    rw [write,set,get,← getElem!_pos,storeWord _ _ _ _ valid (by omega),read,prev]
    split
    · rename_i h; obtain ⟨rfl,rfl⟩ := h; simp [idx]
    · rename_i h
      have eq : (l=lane.val ∧ k < it.start.val) ↔ (l=lane.val ∧ k < next.start.val) := by omega
      rw [if_congr eq rfl rfl]
  · intro it st last stop
    unfold recover_loop2_loop3_loop2.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Wots
