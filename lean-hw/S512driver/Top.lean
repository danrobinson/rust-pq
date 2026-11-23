import S512driver.Funs
import Streamvector.Top
import S512schedule.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream.Eight512
set_option maxRecDepth 16384
open core.core_arch.x86
open slhdsa.X86.S512.Gather (flat flat_length)
private theorem initial (blocks : Array (Array U8 128#usize) 8#usize) (offsets : __m256i)
    (stride : S512.Gather.Stride offsets 128) :
    core.array.from_fn 16#usize S512driverRust.sha512.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i (blocks,offsets,S512.Gather.swapControl)
      ⦃ w => vectorWindow512 w blocks 0 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize _ _
    (fun k x => ∀ j : Fin 8, word64 x j = (Spec.SHA512.schedule (bytes blocks.val[j.val]!.val))[k]!) ?_)
  · intro w hw j k _ hi
    have bound : k < 16 := by simpa using hi
    simpa only [Nat.mod_eq_of_lt bound,Array.getElem!_Nat_eq] using hw k bound j
  intro k hk
  unfold S512driverRust.sha512.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i
  simp only [S512driverRust.sha512.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut,lift,bind_tc_eq,bind_ok,S512driverRust.core.slice.Slice.as_ptr,
    GatherRust.core.slice.Slice.as_ptr,S512driverRust.core.ptr.const_ptr.RawPtrConstT.cast,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,Array.val_to_slice]
  step as ⟨idx,hi⟩
  have total : (flat blocks.val).length = 1024 := by rw [flat_length]; simp
  have bound : idx.val ≤ (flat blocks.val).length := by rw [total,hi]; scalar_tac
  unfold flat at bound
  simp only [S512driverRust.core.ptr.const_ptr.RawPtrConstT.add,GatherRust.core.ptr.const_ptr.RawPtrConstT.add,
    Nat.zero_add,bound,ite_true,bind_ok,S512driverRust.core.core_arch.x86.avx512f._mm512_i32gather_epi64,
    S512driverRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8]
  have gather := gathered512 blocks offsets stride k.val hk
  have pos : idx.val = 8*k.val := by rw [hi,Nat.mul_comm]
  rw [pos]
  rw [← Std.bind_assoc]
  apply WP.spec_bind gather
  intro x hx
  exact (WP.spec_ok _).mpr ⟨hx,rfl⟩


theorem lane (st : Array U64 8#usize) (table : Array (Array U64 8#usize) 80#usize)
    (bs : Array (Array U8 128#usize) 8#usize) (rows : ordered512 table bs 80)
    (it next : core.ops.range.Range Usize) (l : Usize) (bound : l.val < 8)
    (more : core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (some l,next)) :
    S512driverRust.sha512.stream.prescheduled_loop0_loop0.body table it st ⦃ flow => ∃ out,
      flow = ControlFlow.cont (next,out) ∧ slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv st.val) (bytes bs.val[l.val]!.val) ⦄ := by
  exact lane512 st table bs rows it next l bound more

theorem lanes512 (st : Array U64 8#usize) (table : Array (Array U64 8#usize) 80#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (rows : ordered512 table blocks 80) :
    S512driverRust.sha512.stream.prescheduled_loop0_loop0 ⟨0#usize,8#usize⟩ st table ⦃ out =>
      slhdsa.S512.wv out.val = fold512 (slhdsa.S512.wv st.val) blocks.val ⦄ := by
  unfold S512driverRust.sha512.stream.prescheduled_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 8#usize) => 8-p.1.start.val)
    (inv := fun p => p.1.end = 8#usize ∧ p.1.start.val ≤ 8 ∧
      slhdsa.S512.wv p.2.val = fold512 (slhdsa.S512.wv st.val) (blocks.val.take p.1.start.val))
  · rintro ⟨it,state⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    by_cases more : it.start.val < 8
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      step with lane state table blocks rows it next it.start more get as ⟨flow,out,eq,hash⟩
      subst flow
      simp only
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      have inside : it.start.val < blocks.val.length := by simpa using more
      rw [hash,prior,hn,List.take_succ_eq_append_getElem inside,getElem!_pos blocks.val it.start.val inside]
      simp only [fold512,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · unfold S512driverRust.sha512.stream.prescheduled_loop0_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      simpa only [List.take_of_length_le (show blocks.val.length ≤ it.start.val by simp; omega)] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp [fold512]⟩

theorem prescheduled512 (st : Array U64 8#usize) (groups : Slice (Array (Array U8 128#usize) 8#usize)) :
    S512driverRust.sha512.stream.prescheduled st groups ⦃ out => slhdsa.S512.wv out.val = groups.val.foldl (fun s g => fold512 s g.val) (slhdsa.S512.wv st.val) ⦄ := by
  unfold S512driverRust.sha512.stream.prescheduled
  step with offsets512 as ⟨offsets,stride⟩
  rw [← Std.bind_assoc,swap512]
  simp only [bind_ok,SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  unfold S512driverRust.sha512.stream.prescheduled_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter (Array (Array U8 128#usize) 8#usize) × Array U64 8#usize) => groups.length-p.1.i)
    (inv := fun p => p.1.slice = groups ∧ p.1.i ≤ groups.length ∧
      slhdsa.S512.wv p.2.val = (groups.val.take p.1.i).foldl (fun s g => fold512 s g.val) (slhdsa.S512.wv st.val))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold S512driverRust.sha512.stream.prescheduled_loop0.body
    by_cases more : it.i < groups.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some groups.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with initial _ offsets stride as ⟨w,win⟩
      step with schedule w _ win as ⟨ordered,spec⟩
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

end slhdsa.X86.Stream.Eight512
