import Cachepath.NativeShakeWots.PackProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify.Wots
set_option linter.concreteInstances false
variable [machine : Machine]

theorem setRow (s : Matrix machine.width) (row : Usize) (value : Array U64 machine.width) (k l : Nat)
    (fits : row.val<25) :
    cell (s.set row value) k l = if k=row.val then value.val[l]!.bv else cell s k l := by
  unfold cell
  rw [Array.set_val_eq]
  by_cases h : k=row.val
  · subst k; rw [setSame _ _ _ (by simpa)]; simp
  · rw [setOther _ _ _ _ (Ne.symm h)]; simp [h]

def Prefix (n offset : Nat) (sw : Array U64 4#usize) (payload : Nat → Nat → BitVec 64)
    (before after : Matrix machine.width) : Prop :=
  ∀ k l, l<machine.width.val → cell after k l =
    if k<n then sw.val[k]!.bv else if offset≤k ∧ k<offset+n then payload (k-offset) l else cell before k l

theorem fill_prefix (n offset : Usize) (s : Matrix machine.width) (sw skw : Array U64 4#usize)
    (small : n.val≤4) (off : offset.val=n.val+4) :
    fill_prf_loop0 ⟨0#usize,n⟩ s sw skw offset ⦃ st => Prefix n.val offset.val sw (fun j _ => skw.val[j]!.bv) s st ⦄ := by
  unfold fill_prf_loop0
  apply range_fold (fill_prf_loop0.body sw skw offset) n s (fun i st => Prefix i offset.val sw (fun j _ => skw.val[j]!.bv) s st)
  · intro k l hl; simp
  · intro it st stop live prev
    unfold fill_prf_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨w,read⟩
    step as ⟨st',upd⟩
    step as ⟨sk,sv⟩
    step as ⟨r,rv⟩
    step as ⟨out,set⟩
    refine ⟨next,out,rfl,ends.trans stop,idx,?_⟩
    intro k l hl
    rw [set,broadcast _ _ _ _ _ (by omega) hl,upd,broadcast _ _ _ _ _ (by omega) hl,prev k l hl,rv,read,sv]
    simp only [← getElem!_pos,idx]
    split_ifs <;> first | rfl | (rw [show offset.val+it.start.val-offset.val=it.start.val by omega]) | omega | (congr 2 <;> omega) | (subst_vars; simp [Nat.add_sub_cancel_left])
  · intro it st last stop
    unfold fill_prf_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem refill_prefix (n offset : Usize) (s : Matrix machine.width) (sw : Array U64 4#usize)
    (small : n.val≤4) (off : offset.val=n.val+4) :
    refill_short_inplace_loop0 ⟨0#usize,n⟩ s sw offset ⦃ st => Prefix n.val offset.val sw (cell s) s st ⦄ := by
  unfold refill_short_inplace_loop0
  apply range_fold (refill_short_inplace_loop0.body sw offset) n s (fun i st => Prefix i offset.val sw (cell s) s st)
  · intro k l hl; simp
  · intro it st stop live prev
    unfold refill_short_inplace_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨row,value⟩
    step as ⟨r,rv⟩
    step as ⟨st',upd⟩
    step as ⟨w,read⟩
    step as ⟨out,set⟩
    refine ⟨next,out,rfl,ends.trans stop,idx,?_⟩
    intro k l hl
    rw [set,broadcast _ _ _ _ _ (by omega) hl,upd,setRow _ _ _ _ _ (by omega),prev k l hl,rv,read,value]
    simp only [← getElem!_pos,idx]
    have before := prev it.start.val l hl
    simp only [lt_self_iff_false,ite_false,ite_eq_right (by omega : ¬(offset.val ≤ it.start.val ∧ it.start.val < offset.val+it.start.val))] at before
    change cell st it.start.val l = cell s it.start.val l at before
    unfold cell at before
    rw [before]
    simp only [Nat.add_sub_cancel_left,cell] at *
    split_ifs <;> first | rfl | (rw [show offset.val+it.start.val-offset.val=it.start.val by omega]) | omega | (congr 2 <;> omega) | (subst_vars; simp [Nat.add_sub_cancel_left])
  · intro it st last stop
    unfold refill_short_inplace_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeShakeWots
