import Streamvector.Lanes
import Streamvector.Table
import Streamvector.Groups
open Aeneas Aeneas.Std Result
open core.core_arch.x86
namespace slhdsa.X86.Stream
set_option maxRecDepth 8192

theorem table256 (w : Array Reg 16#usize) (table : Array (Array U32 16#usize) 64#usize)
    (blocks : Array (Array U8 64#usize) 16#usize) (old : vectorWindow256 w blocks 0) :
    StreamVectorRust.sha256.stream.prescheduled_loop0_loop0 ⟨0#usize,64#usize⟩ table w ⦃ out => ordered256 out blocks 64 ⦄ := by
  unfold StreamVectorRust.sha256.stream.prescheduled_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array (Array U32 16#usize) 64#usize × Array Reg 16#usize) => 64-p.1.start.val)
    (inv := fun p => p.1.end = 64#usize ∧ p.1.start.val ≤ 64 ∧ vectorWindow256 p.2.2 blocks p.1.start.val ∧ ordered256 p.2.1 blocks p.1.start.val)
  · rintro ⟨it,rows,ring⟩ ⟨he,hb,window,prior⟩
    simp only at he hb window prior
    by_cases more : it.start.val < 64
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      step with scheduleBody256 it next it.start ring rows blocks more get window prior as ⟨flow,rows',ring',eq,win,ord⟩
      subst flow
      simp only
      exact ⟨he'.trans he,by omega,hn ▸ win,hn ▸ ord,by omega⟩
    · unfold StreamVectorRust.sha256.stream.prescheduled_loop0_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      exact (show it.start.val = 64 by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,old,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

theorem lanes256 (st : Array U32 8#usize) (table : Array (Array U32 16#usize) 64#usize)
    (blocks : Array (Array U8 64#usize) 16#usize) (rows : ordered256 table blocks 64) :
    StreamVectorRust.sha256.stream.prescheduled_loop0_loop1 ⟨0#usize,16#usize⟩ st table ⦃ out =>
      slhdsa.wv out.val = fold256 (slhdsa.wv st.val) blocks.val ⦄ := by
  unfold StreamVectorRust.sha256.stream.prescheduled_loop0_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U32 8#usize) => 16-p.1.start.val)
    (inv := fun p => p.1.end = 16#usize ∧ p.1.start.val ≤ 16 ∧
      slhdsa.wv p.2.val = fold256 (slhdsa.wv st.val) (blocks.val.take p.1.start.val))
  · rintro ⟨it,state⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    by_cases more : it.start.val < 16
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      step with lane256 state table blocks rows it next it.start more get as ⟨flow,out,eq,hash⟩
      subst flow
      simp only
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      have inside : it.start.val < blocks.val.length := by simpa using more
      rw [hash,prior,hn,List.take_succ_eq_append_getElem inside,getElem!_pos blocks.val it.start.val inside]
      simp only [fold256,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · unfold StreamVectorRust.sha256.stream.prescheduled_loop0_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      simpa only [List.take_of_length_le (show blocks.val.length ≤ it.start.val by simp; omega)] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp [fold256]⟩

theorem prescheduled256 (st : Array U32 8#usize) (groups : Slice (Array (Array U8 64#usize) 16#usize)) :
    StreamVectorRust.sha256.stream.prescheduled st groups ⦃ out => slhdsa.wv out.val = groups.val.foldl (fun s g => fold256 s g.val) (slhdsa.wv st.val) ⦄ := by
  unfold StreamVectorRust.sha256.stream.prescheduled
  step with offsets256 as ⟨offsets,stride⟩
  rw [← Std.bind_assoc,swap256]
  simp only [bind_ok,SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  unfold StreamVectorRust.sha256.stream.prescheduled_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter (Array (Array U8 64#usize) 16#usize) × Array U32 8#usize) => groups.length-p.1.i)
    (inv := fun p => p.1.slice = groups ∧ p.1.i ≤ groups.length ∧
      slhdsa.wv p.2.val = (groups.val.take p.1.i).foldl (fun s g => fold256 s g.val) (slhdsa.wv st.val))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold StreamVectorRust.sha256.stream.prescheduled_loop0.body
    by_cases more : it.i < groups.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some groups.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with vectorInitial256 _ offsets stride as ⟨w,win⟩
      step with table256 w _ _ win as ⟨ordered,spec⟩
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

theorem table512 (w : Array Reg 16#usize) (table : Array (Array U64 8#usize) 80#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (old : vectorWindow512 w blocks 0) :
    StreamVectorRust.sha512.stream.prescheduled_loop0_loop0 ⟨0#usize,80#usize⟩ table w ⦃ out => ordered512 out blocks 80 ⦄ := by
  unfold StreamVectorRust.sha512.stream.prescheduled_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array (Array U64 8#usize) 80#usize × Array Reg 16#usize) => 80-p.1.start.val)
    (inv := fun p => p.1.end = 80#usize ∧ p.1.start.val ≤ 80 ∧ vectorWindow512 p.2.2 blocks p.1.start.val ∧ ordered512 p.2.1 blocks p.1.start.val)
  · rintro ⟨it,rows,ring⟩ ⟨he,hb,window,prior⟩
    simp only at he hb window prior
    by_cases more : it.start.val < 80
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      step with scheduleBody512 it next it.start ring rows blocks more get window prior as ⟨flow,rows',ring',eq,win,ord⟩
      subst flow
      simp only
      exact ⟨he'.trans he,by omega,hn ▸ win,hn ▸ ord,by omega⟩
    · unfold StreamVectorRust.sha512.stream.prescheduled_loop0_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      exact (show it.start.val = 80 by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,old,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

theorem lanes512 (st : Array U64 8#usize) (table : Array (Array U64 8#usize) 80#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (rows : ordered512 table blocks 80) :
    StreamVectorRust.sha512.stream.prescheduled_loop0_loop1 ⟨0#usize,8#usize⟩ st table ⦃ out =>
      slhdsa.S512.wv out.val = fold512 (slhdsa.S512.wv st.val) blocks.val ⦄ := by
  unfold StreamVectorRust.sha512.stream.prescheduled_loop0_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 8#usize) => 8-p.1.start.val)
    (inv := fun p => p.1.end = 8#usize ∧ p.1.start.val ≤ 8 ∧
      slhdsa.S512.wv p.2.val = fold512 (slhdsa.S512.wv st.val) (blocks.val.take p.1.start.val))
  · rintro ⟨it,state⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    by_cases more : it.start.val < 8
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      step with lane512 state table blocks rows it next it.start more get as ⟨flow,out,eq,hash⟩
      subst flow
      simp only
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      have inside : it.start.val < blocks.val.length := by simpa using more
      rw [hash,prior,hn,List.take_succ_eq_append_getElem inside,getElem!_pos blocks.val it.start.val inside]
      simp only [fold512,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · unfold StreamVectorRust.sha512.stream.prescheduled_loop0_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      simpa only [List.take_of_length_le (show blocks.val.length ≤ it.start.val by simp; omega)] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp [fold512]⟩

theorem prescheduled512 (st : Array U64 8#usize) (groups : Slice (Array (Array U8 128#usize) 8#usize)) :
    StreamVectorRust.sha512.stream.prescheduled st groups ⦃ out => slhdsa.S512.wv out.val = groups.val.foldl (fun s g => fold512 s g.val) (slhdsa.S512.wv st.val) ⦄ := by
  unfold StreamVectorRust.sha512.stream.prescheduled
  step with offsets512 as ⟨offsets,stride⟩
  rw [← Std.bind_assoc,swap512]
  simp only [bind_ok,SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  unfold StreamVectorRust.sha512.stream.prescheduled_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter (Array (Array U8 128#usize) 8#usize) × Array U64 8#usize) => groups.length-p.1.i)
    (inv := fun p => p.1.slice = groups ∧ p.1.i ≤ groups.length ∧
      slhdsa.S512.wv p.2.val = (groups.val.take p.1.i).foldl (fun s g => fold512 s g.val) (slhdsa.S512.wv st.val))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold StreamVectorRust.sha512.stream.prescheduled_loop0.body
    by_cases more : it.i < groups.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some groups.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with vectorInitial512 _ offsets stride as ⟨w,win⟩
      step with table512 w _ _ win as ⟨ordered,spec⟩
      step with lanes512 state ordered _ spec as ⟨out,hash⟩
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

end slhdsa.X86.Stream
