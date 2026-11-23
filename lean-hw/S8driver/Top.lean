import S8driver.Lane
import Streamround.Blocks
set_option maxRecDepth 24000
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream.Eight
theorem lanes256 (st : Array U32 8#usize) (table : Array (Array U32 8#usize) 64#usize)
    (blocks : Array (Array U8 64#usize) 8#usize) (rows : ordered256 table blocks 64) :
    S8driverRust.sha256.stream.prescheduled_loop0_loop0 ⟨0#usize,8#usize⟩ st table ⦃ out =>
      slhdsa.wv out.val = fold256 (slhdsa.wv st.val) blocks.val ⦄ := by
  unfold S8driverRust.sha256.stream.prescheduled_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U32 8#usize) => 8-p.1.start.val)
    (inv := fun p => p.1.end = 8#usize ∧ p.1.start.val ≤ 8 ∧
      slhdsa.wv p.2.val = fold256 (slhdsa.wv st.val) (blocks.val.take p.1.start.val))
  · rintro ⟨it,state⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    by_cases more : it.start.val < 8
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      step with lane256 state table blocks rows it next it.start more get as ⟨flow,out,eq,hash⟩
      subst flow
      simp only
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      have inside : it.start.val < blocks.val.length := by simpa using more
      rw [hash,prior,hn,List.take_succ_eq_append_getElem inside,getElem!_pos blocks.val it.start.val inside]
      simp only [fold256,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · unfold S8driverRust.sha256.stream.prescheduled_loop0_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      simpa only [List.take_of_length_le (show blocks.val.length ≤ it.start.val by simp; omega)] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp [fold256]⟩

theorem prescheduled256 (st : Array U32 8#usize) (groups : Slice (Array (Array U8 64#usize) 8#usize)) :
    S8driverRust.sha256.stream.prescheduled st groups ⦃ out => slhdsa.wv out.val = groups.val.foldl (fun s g => fold256 s g.val) (slhdsa.wv st.val) ⦄ := by
  unfold S8driverRust.sha256.stream.prescheduled
  simp only [bind_ok,SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  unfold S8driverRust.sha256.stream.prescheduled_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter (Array (Array U8 64#usize) 8#usize) × Array U32 8#usize) => groups.length-p.1.i)
    (inv := fun p => p.1.slice = groups ∧ p.1.i ≤ groups.length ∧
      slhdsa.wv p.2.val = (groups.val.take p.1.i).foldl (fun s g => fold256 s g.val) (slhdsa.wv st.val))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold S8driverRust.sha256.stream.prescheduled_loop0.body
    by_cases more : it.i < groups.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some groups.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with table_fips _ as ⟨ordered,spec⟩
      step with lanes256 state ordered _ spec as ⟨out,hash⟩
      refine ⟨slice,by change it.i+1 ≤ groups.length; omega,?_,by change groups.length-(it.i+1) < groups.length-it.i; omega⟩
      rw [hash,prior]
      change _ = (groups.val.take (it.i+1)).foldl _ _
      rw [List.take_succ_eq_append_getElem more,List.foldl_append]
      rfl
    · have get : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok,step_simps]
      simpa [List.take_of_length_le (show groups.val.length ≤ it.i from Nat.le_of_not_gt more)] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp⟩

end slhdsa.X86.Stream.Eight
