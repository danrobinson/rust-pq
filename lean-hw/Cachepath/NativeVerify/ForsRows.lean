import Cachepath.NativeVerify.ForsPayload

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem leaf_payload (s : Matrix machine.width) (n offset lane : Usize) (blk : Slice U8)
    (within : offset.val+n.val≤25) (inside : lane.val<machine.width.val) (fit : n.val*8≤blk.length) :
    recover_loop0_loop2_loop0 ⟨0#usize,n⟩ offset s lane blk ⦃ out =>
      ∀ k<25, ∀ j<machine.width.val, cell out k j =
        if j=lane.val ∧ offset.val≤k ∧ k<offset.val+n.val then inputWord blk.val (k-offset.val) else cell s k j ⦄ := by
  unfold recover_loop0_loop2_loop0
  apply range_fold (recover_loop0_loop2_loop0.body offset lane blk) n s (fun size out =>
    ∀ k<25, ∀ j<machine.width.val, cell out k j =
      if j=lane.val ∧ offset.val≤k ∧ k<offset.val+size then inputWord blk.val (k-offset.val) else cell s k j)
  · intro k hk j hj
    simp
  · intro it state stop live prev
    unfold recover_loop0_loop2_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step with word_spec blk it.start (by omega) as ⟨v,word⟩
    step as ⟨r,rv⟩
    step as ⟨row,restore,read,back⟩
    step as ⟨row',upd⟩
    refine ⟨next,_,rfl,ends.trans stop,inc,?_⟩
    intro k hk j hj
    rw [back,upd,read,← getElem!_pos,cell_write _ _ _ _ (by omega) inside,prev k hk j hj,rv,word,inc]
    by_cases hit : k=offset.val+it.start.val ∧ j=lane.val
    · obtain ⟨rfl,rfl⟩ := hit
      simp [inputWord]
    · rw [ite_eq_right hit]
      apply if_congr _ rfl rfl
      omega
  · intro it state last stop
    unfold recover_loop0_loop2_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem seed_rows (s : Matrix machine.width) (n : Usize) (sw : Array U64 4#usize) (cap : n.val≤4) :
    recover_loop0_loop1 ⟨0#usize,n⟩ sw s ⦃ out =>
      ∀ k<25, ∀ j<machine.width.val, cell out k j =
        if k<n.val then sw.val[k]!.bv else cell s k j ⦄ := by
  unfold recover_loop0_loop1
  apply range_fold (recover_loop0_loop1.body sw) n s (fun size out =>
    ∀ k<25, ∀ j<machine.width.val, cell out k j = if k<size then sw.val[k]!.bv else cell s k j)
  · simp
  · intro it state stop live prev
    unfold recover_loop0_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨w,read⟩
    step as ⟨st,upd⟩
    refine ⟨next,_,rfl,ends.trans stop,inc,?_⟩
    intro k hk j hj
    rw [upd,cache.builder.nativeShake.Vector.Fused.write_tag _ _ _ (by omega) k j hj,prev k hk j hj,read,← getElem!_pos]
    by_cases same : k=it.start.val
    · subst k; simp [inc]
    · simp [same,show (k < next.start.val) ↔ k < it.start.val by omega]
  · intro it st last stop
    unfold recover_loop0_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

/-- Each compression round saves its input digest words before restoring the public seed. -/
theorem snapshot (s : Matrix machine.width) (cur : Array (Array U64 machine.width) 4#usize)
    (n : Usize) (sw : Array U64 4#usize) (cap : n.val≤4) :
    recover_loop0_loop4_loop0 ⟨0#usize,n⟩ sw s cur ⦃ out saved =>
      (∀ k<25, ∀ j<machine.width.val, cell out k j =
        if k<n.val then sw.val[k]!.bv else cell s k j) ∧
      (∀ k<n.val, saved.val[k]! = s.val[k]!) ⦄ := by
  unfold recover_loop0_loop4_loop0
  let body := fun (it : Range) (v : Matrix machine.width × Array (Array U64 machine.width) 4#usize) =>
    recover_loop0_loop4_loop0.body sw it v.1 v.2
  apply range_fold body n (s,cur) (fun i v =>
    (∀ k<25, ∀ j<machine.width.val, cell v.1 k j = if k < i then sw.val[k]!.bv else cell s k j) ∧
    (∀ k < i, v.2.val[k]! = s.val[k]!))
  · simp
  · rintro it ⟨state,saved⟩ stop live ⟨prev,old⟩
    dsimp only at prev old
    unfold body recover_loop0_loop4_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨row,read⟩
    step as ⟨saved',wrote⟩
    step as ⟨w,word⟩
    step as ⟨st,upd⟩
    refine ⟨next,(st,saved'),rfl,ends.trans stop,inc,?_,?_⟩
    · intro k hk j hj
      rw [upd,cache.builder.nativeShake.Vector.Fused.write_tag _ _ _ (by omega) k j hj,prev k hk j hj,word,← getElem!_pos]
      by_cases same : k=it.start.val
      · subst k; simp [inc]
      · simp [same,show (k < next.start.val) ↔ k < it.start.val by omega]
    · intro k hk
      rw [wrote,Array.set_val_eq]
      by_cases same : k=it.start.val
      · subst k
        rw [setSame _ _ _ (by simp;omega),read,← getElem!_pos]
        apply Aeneas.Std.Array.ext _ _
        apply List.ext_getElem
        · simp
        · intro j hj hj'
          have h := prev it.start.val (by omega) j (by simpa using hj)
          simp only [lt_self_iff_false,ite_false,cell] at h
          rw [← getElem!_pos (state.val[it.start.val]!).val j hj,← getElem!_pos (s.val[it.start.val]!).val j hj']
          exact UScalar.eq_of_val_eq (congrArg BitVec.toNat h)
      · rw [setOther _ _ _ _ (Ne.symm same),old k (by omega)]
  · rintro it ⟨st,saved⟩ last stop
    unfold body recover_loop0_loop4_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Fors
