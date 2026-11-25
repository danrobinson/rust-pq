import Cachepath.NativeVerify.ForsFusedProgram
import Cachepath.NativeVerify.ActiveHashRows
import Cachepath.NativeShakeWots.Hashes
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.ForsFused
open ShakeBatch NativeShakeWots NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [machine : Machine]

theorem tags (indices : Array U32 machine.width) (active : Usize)
    (bound : active.val ≤ machine.width.val) :
    fused_loop0 ⟨0#usize,active⟩ indices (Array.repeat machine.width 0#u64) ⦃ out =>
      ∀ j<active.val, out.val[j]!.bv=wordTag indices.val[j]! ⦄ := by
  unfold fused_loop0
  apply range_fold (fused_loop0.body indices) active _ (fun i st => ∀ j < i, st.val[j]!.bv=wordTag indices.val[j]!)
  · simp
  · intro it st stop live prev
    unfold fused_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨idx,idxRead⟩
    simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
    step as ⟨hi,_,bits⟩
    step as ⟨out,write⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    intro j hj
    rw [write,Array.set_val_eq]
    by_cases eq : j=it.start.val
    · subst j
      rw [setSame _ _ _ (by simpa using live.trans_le bound)]
      rw [idxRead,← getElem!_pos] at bits
      exact bits
    · rw [setOther _ _ _ _ (Ne.symm eq)]
      exact prev j (by omega)
  · intro it st last stop
    unfold fused_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem read_lanes (N : Usize) (s : Matrix machine.width) (active n : Usize)
    (b : active.val≤machine.width.val) (small : N.val≤32) (align : N.val%8=0) (nv : n.val=N.val/8) :
    fused_loop4 ⟨0#usize,n⟩ active s (Array.repeat machine.width (Array.repeat N 0#u8)) ⦃ out =>
      ∀ j < active.val, bytes out.val[j]!.val = digest N s j ⦄ := by
  have h := ActiveHash.read_digest N s active b (by omega) align
  unfold ActiveHash.read_active at h
  have d : N / 8#usize ⦃ t => t.val=N.val/8 ⦄ := by step; assumption
  obtain ⟨t,eq,v⟩ := spec_imp_exists d
  rw [eq] at h
  simp only [bind_ok] at h
  have same : n=t := by scalar_tac
  subst n
  exact h

end slhdsa.NativeVerify.ForsFused
