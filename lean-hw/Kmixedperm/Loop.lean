import Kmixedperm.Restore
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kmixedperm
open KeccakRegisters KmixedpermRust
open KmixedpermRust.shake256.parallel
set_option maxHeartbeats 2000000
theorem rounds (one : ∀ (a : Rows) (rc : U64), mixed.round a rc ⦃ out => ∀ j, lane out j = round (lane a j) rc.bv ⦄)
    (a : Rows) (keys : Slice U64) :
    mixed.permute_loop0 ⟨keys,0⟩ a ⦃ out => ∀ j, lane out j = (keys.val.map (·.bv)).foldl round (lane a j) ⦄ := by
  unfold mixed.permute_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter U64 × Rows) => keys.length-p.1.i)
    (inv := fun p => p.1.slice = keys ∧ p.1.i ≤ keys.length ∧
      ∀ j, lane p.2 j = ((keys.val.take p.1.i).map (·.bv)).foldl round (lane a j))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold mixed.permute_loop0.body
    by_cases more : it.i < keys.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some keys.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with one state _ as ⟨out,post⟩
      refine ⟨slice,by change it.i+1 ≤ keys.length; omega,?_,by change keys.length-(it.i+1) < keys.length-it.i; omega⟩
      intro j
      rw [post j,prior j]
      change _ = (((keys.val.take (it.i+1)).map _).foldl _ _)
      rw [List.take_succ_eq_append_getElem more,List.map_append,List.foldl_append]
      rfl
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length] at *
      rw [doneIt]
      simp only [step_simps]
      simpa [show it.i=keys.length by omega,Slice.length] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp⟩


theorem permute_of_round (one : ∀ (a : Rows) (rc : U64),
    mixed.round a rc ⦃ out => ∀ j, lane out j = round (lane a j) rc.bv ⦄) (words : Matrix 3#usize) :
    mixed.permute words ⦃ out => ∀ j, view out j = permute (view words j) ⦄ := by
  unfold mixed.permute
  step with pack words as ⟨a,ha⟩
  simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  step with rounds one a _ as ⟨r,hr⟩
  step with restore words r as ⟨out,ho⟩
  rename_i j
  rw [ho,hr,ha]
  have constants : KmixedpermRust.shake256.RC.val.map (·.bv) = rc.toList := by unfold KmixedpermRust.shake256.RC rc; rfl
  simp only [Slice.from_val]
  change (KmixedpermRust.shake256.RC.val.map (·.bv)).foldl round _ = _
  rw [constants]
  rfl
end slhdsa.Kmixedperm
