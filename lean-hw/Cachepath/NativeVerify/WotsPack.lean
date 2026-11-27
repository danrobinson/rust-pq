import Cachepath.NativeVerify.WotsLoad
import Cachepath.WotsFusedLayout

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

theorem broadcast (s : Matrix machine.width) (row : Usize) (w : U64) (k l : Nat)
    (inside : row.val < 25) (valid : l<machine.width.val) :
    cell (s.set row (Array.repeat machine.width w)) k l = if k=row.val then w.bv else cell s k l := by
  unfold cell
  rw [Array.set_val_eq]
  by_cases h : k=row.val
  · subst k; rw [setSame _ _ _ (by simpa),Array.repeat_val]; simp [valid]
  · rw [setOther _ _ _ _ (Ne.symm h)]; simp [h]

theorem pack_word (s : Matrix machine.width) (offset j active : Usize) (values : LaneValues machine.width)
    (room : active.val≤machine.width.val) (capacity : j.val<4) (fits : offset.val+j.val<25) :
    recover_loop2_loop0_loop0 ⟨0#usize,active⟩ offset values s j ⦃ st => ∀ k l, cell st k l =
      if k=offset.val+j.val ∧ l<active.val then laneWord values l j.val else cell s k l ⦄ := by
  unfold recover_loop2_loop0_loop0
  apply range_fold (recover_loop2_loop0_loop0.body offset values j) active s (fun i st => ∀ k l, cell st k l =
    if k=offset.val+j.val ∧ l < i then laneWord values l j.val else cell s k l)
  · simp
  · intro it st stop live prev
    unfold recover_loop2_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨vs,vi⟩
    step as ⟨w,word⟩
    step as ⟨r,rv⟩
    step as ⟨row,back,get,write⟩
    step as ⟨out,set⟩
    refine ⟨next,_,rfl,ends.trans stop,idx,?_⟩
    intro k l
    have read : w.bv=laneWord values it.start.val j.val := by rw [word,← getElem!_pos,vi,← getElem!_pos];rfl
    rw [write,set,get,← getElem!_pos,cell_write _ _ _ _ (by omega) (by omega),read,prev]
    simp only [rv,idx]
    split_ifs <;> first | rfl | omega | (congr 1 <;> omega)
  · intro it st last stop
    unfold recover_loop2_loop0_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem pack_seed_payload (s : Matrix machine.width) (offset n active : Usize) (values : LaneValues machine.width)
    (seed : Array U64 4#usize) (room : active.val≤machine.width.val) (cap : n.val≤4)
    (disjoint : n.val≤offset.val) (fits : offset.val+n.val≤25) :
    recover_loop2_loop0 ⟨0#usize,n⟩ offset seed active values s ⦃ st => ∀ k, ∀ l < machine.width.val,
      cell st k l = if k<n.val then seed.val[k]!.bv else
        if l<active.val ∧ offset.val≤k ∧ k<offset.val+n.val then laneWord values l (k-offset.val) else cell s k l ⦄ := by
  unfold recover_loop2_loop0
  apply range_fold (recover_loop2_loop0.body offset seed active values) n s (fun i st => ∀ k, ∀ l < machine.width.val,
    cell st k l = if k < i then seed.val[k]!.bv else
      if l<active.val ∧ offset.val≤k ∧ k<offset.val+i then laneWord values l (k-offset.val) else cell s k l)
  · intro k l hl; simp
  · intro it st stop live prev
    unfold recover_loop2_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨w,read⟩
    step as ⟨st',upd⟩
    step with pack_word st' offset it.start active values room (by omega) (by omega) as ⟨out,packed⟩
    refine ⟨next,out,rfl,ends.trans stop,idx,?_⟩
    intro k l hl
    rw [packed,upd,broadcast _ _ _ _ _ (by omega) hl,prev k l hl,read,← getElem!_pos]
    simp only [idx]
    split_ifs <;> first | rfl | omega | (congr 1 <;> omega) | (subst_vars; rfl)
  · intro it st last stop
    unfold recover_loop2_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem pack_tags (s : Matrix machine.width) (n active : Usize) (ids : Array Usize machine.width)
    (steps : Array U32 machine.width) (room : active.val≤machine.width.val) (cap : n.val+3<25) :
    recover_loop2_loop1 ⟨0#usize,active⟩ n ids steps s ⦃ st => ∀ k l, cell st k l =
      if k=n.val+3 ∧ l<active.val then addressLow (UScalar.cast .U32 ids.val[l]!) ||| wordTag steps.val[l]!
      else cell s k l ⦄ := by
  unfold recover_loop2_loop1
  apply range_fold (recover_loop2_loop1.body n ids steps) active s (fun i st => ∀ k l, cell st k l =
    if k=n.val+3 ∧ l < i then addressLow (UScalar.cast .U32 ids.val[l]!) ||| wordTag steps.val[l]! else cell s k l)
  · simp
  · intro it st stop live prev
    unfold recover_loop2_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨id,readId⟩
    simp only [lift,bind_ok,ShakeBatch.core.num.U32.swap_bytes]
    step as ⟨digit,readStep⟩
    step as ⟨hi,_,bits⟩
    step as ⟨r,rv⟩
    step as ⟨row,back,get,write⟩
    step as ⟨out,upd⟩
    refine ⟨next,_,rfl,ends.trans stop,idx,?_⟩
    intro k l
    rw [write,upd,get,← getElem!_pos,cell_write _ _ _ _ (by omega) (by omega),prev]
    simp only [rv,idx]
    split
    · rename_i h; obtain ⟨rfl,rfl⟩ := h
      rw [ite_eq_left ⟨rfl,by omega⟩]
      rw [← getElem!_pos] at readId readStep
      rw [← readId,← readStep]
      exact congrArg (fun v => addressLow (UScalar.cast .U32 id) ||| v) bits
    · rename_i h
      have eq : (k=n.val+3 ∧ l < it.start.val) ↔ (k=n.val+3 ∧ l < it.start.val+1) := by omega
      rw [if_congr eq rfl rfl]
  · intro it st last stop
    unfold recover_loop2_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Wots
