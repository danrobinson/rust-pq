import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem write_secrets {N : Usize} (rows : Rows N) (first stride active : Usize)
    (sig : Buffer) (fit : (first.val+active.val)*stride.val ≤ sig.length)
    (width : active.val ≤ machine.width.val) (positive : 0 < N.val) (within : 0+N.val ≤ stride.val) :
    shake.fors_batch.sign_loop0_loop0 ⟨0#usize,active⟩ stride sig first rows ⦃ out =>
      Scattered rows first.val stride.val 0 active.val sig out ⦄ := by
  unfold shake.fors_batch.sign_loop0_loop0
  apply range_fold (shake.fors_batch.sign_loop0_loop0.body stride first rows) active sig (fun c out => Scattered rows first.val stride.val 0 c sig out)
  · simp [Scattered] <;> omega
  · intro it cur he hi prior
    have lt : it.start.val < it.end.val := he.symm ▸ hi
    have room := Nat.mul_le_mul_right stride.val (show first.val+it.start.val+1 ≤ first.val+active.val by omega)
    have cap : (first.val+it.start.val+1)*stride.val ≤ sig.length := room.trans fit
    have raw : (first.val+it.start.val)*stride.val+stride.val ≤ sig.length := by simpa only [Nat.add_mul,Nat.one_mul] using cap
    have fit' := prior.1
    have max : sig.length ≤ Usize.max := by simp
    have minStride : 1 ≤ stride.val := by omega
    have bounded : first.val+it.start.val ≤ Usize.max := by
      have b := Nat.mul_le_mul_left (first.val+it.start.val) minStride
      simp only [Nat.mul_one] at b
      omega
    unfold shake.fors_batch.sign_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,nxt,ho,hn,hend⟩
    simp only [ho]
    step as ⟨r,rv⟩
    step as ⟨pos,pv⟩
    step as ⟨start,sv⟩
    step as ⟨stop,ev⟩
    step as ⟨dst,back,data,len,save⟩
    step as ⟨row,get⟩
    try simp only [lift,bind_ok]
    step as ⟨w,cp⟩
    all_goals try scalar_tac
    refine ⟨nxt,_,rfl,hend.trans he,hn,?_⟩
    rw [hn]
    apply scatter_step _ _ _ _ _ _ _ _ cap within prior
    rw [save,cp,Array.val_to_slice,get,← getElem!_pos]
    simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val]
    simp only [pv,rv,Nat.add_zero]
  · intro it cur atEnd he
    have stop := core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he];omega)
    obtain ⟨⟨o,nxt⟩,run,none,_⟩ := spec_imp_exists stop
    unfold shake.fors_batch.sign_loop0_loop0.body
    simp only [run,bind_ok,none]
    rfl

theorem write_siblings {N : Usize} (rows : Rows N) (first stride active : Usize) (level : U32)
    (sig : Buffer) (fit : (first.val+active.val)*stride.val ≤ sig.length)
    (width : active.val ≤ machine.width.val) (positive : 0 < N.val) (within : ((level.val+1)*N.val)+N.val ≤ stride.val) :
    shake.fors_batch.sign_loop0_loop1_loop0 ⟨0#usize,active⟩ stride sig first level rows ⦃ out =>
      Scattered rows first.val stride.val ((level.val+1)*N.val) active.val sig out ⦄ := by
  unfold shake.fors_batch.sign_loop0_loop1_loop0
  apply range_fold (shake.fors_batch.sign_loop0_loop1_loop0.body stride first level rows) active sig (fun c out => Scattered rows first.val stride.val ((level.val+1)*N.val) c sig out)
  · simp [Scattered] <;> omega
  · intro it cur he hi prior
    have lt : it.start.val < it.end.val := he.symm ▸ hi
    have room := Nat.mul_le_mul_right stride.val (show first.val+it.start.val+1 ≤ first.val+active.val by omega)
    have cap : (first.val+it.start.val+1)*stride.val ≤ sig.length := room.trans fit
    have raw : (first.val+it.start.val)*stride.val+stride.val ≤ sig.length := by simpa only [Nat.add_mul,Nat.one_mul] using cap
    have fit' := prior.1
    have max : sig.length ≤ Usize.max := by simp
    have minStride : 1 ≤ stride.val := by omega
    have bounded : first.val+it.start.val ≤ Usize.max := by
      have b := Nat.mul_le_mul_left (first.val+it.start.val) minStride
      simp only [Nat.mul_one] at b
      omega
    unfold shake.fors_batch.sign_loop0_loop1_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,nxt,ho,hn,hend⟩
    simp only [ho]
    step as ⟨r,rv⟩
    step as ⟨pos,pv⟩
    try simp only [lift,bind_ok]
    have lv : (UScalar.cast .Usize level).val=level.val := by scalar_tac
    have levelOK : level.val+1 ≤ Usize.max := by
      have h := Nat.mul_le_mul_left (level.val+1) positive
      simp only [Nat.mul_one] at h
      omega
    step as ⟨l,lev⟩
    step as ⟨off,offv⟩
    step as ⟨start,sv⟩
    step as ⟨stop,ev⟩
    step as ⟨dst,back,data,len,save⟩
    step as ⟨row,get⟩
    try simp only [lift,bind_ok]
    step as ⟨w,cp⟩
    all_goals try scalar_tac
    refine ⟨nxt,_,rfl,hend.trans he,hn,?_⟩
    rw [hn]
    apply scatter_step _ _ _ _ _ _ _ _ cap within prior
    rw [save,cp,Array.val_to_slice,get,← getElem!_pos]
    simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val]
    simp only [sv,pv,rv,offv,lev,lv]
  · intro it cur atEnd he
    have stop := core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he];omega)
    obtain ⟨⟨o,nxt⟩,run,none,_⟩ := spec_imp_exists stop
    unfold shake.fors_batch.sign_loop0_loop1_loop0.body
    simp only [run,bind_ok,none]
    rfl
end slhdsa.ShakeBatch
