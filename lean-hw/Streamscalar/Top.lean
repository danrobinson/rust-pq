import Streamscalar.Block
import Streamround.Blocks
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream
set_option maxRecDepth 8192

theorem scalar256 (st : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :
    StreamScalarRust.sha256.stream.scalar st blocks ⦃ out =>
      slhdsa.wv out.val = fold256 (slhdsa.wv st.val) blocks.val ⦄ := by
  unfold StreamScalarRust.sha256.stream.scalar
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  unfold StreamScalarRust.sha256.stream.scalar_loop0
  apply loop.spec_decr_nat
    (measure := fun p : core.slice.iter.Iter (Array U8 64#usize) × Array U32 8#usize => blocks.length-p.1.i)
    (inv := fun p => p.1.slice = blocks ∧ p.1.i ≤ blocks.length ∧
      slhdsa.wv p.2.val = fold256 (slhdsa.wv st.val) (blocks.val.take p.1.i))
  · rintro ⟨it,state⟩ ⟨slice,bound,prev⟩
    simp only at slice bound prev
    by_cases more : it.i < blocks.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some blocks.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      step with block256 state it next _ get as ⟨flow,out,eq,hash⟩
      subst flow
      simp only
      refine ⟨slice,by change it.i+1 ≤ blocks.length; omega,?_,by change blocks.length-(it.i+1) < blocks.length-it.i; omega⟩
      rw [hash,prev]
      rw [List.take_succ_eq_append_getElem more]
      simp only [fold256,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length]
      simp only
      unfold StreamScalarRust.sha256.stream.scalar_loop0.body
      rw [doneIt]
      simp only [bind_ok,step_simps]
      simpa [List.take_of_length_le (show blocks.val.length ≤ it.i by exact Nat.le_of_not_gt more)] using prev
  · exact ⟨rfl,Nat.zero_le _,by simp [fold256]⟩

theorem scalar512 (st : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :
    StreamScalarRust.sha512.stream.scalar st blocks ⦃ out =>
      slhdsa.S512.wv out.val = fold512 (slhdsa.S512.wv st.val) blocks.val ⦄ := by
  unfold StreamScalarRust.sha512.stream.scalar
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  unfold StreamScalarRust.sha512.stream.scalar_loop0
  apply loop.spec_decr_nat
    (measure := fun p : core.slice.iter.Iter (Array U8 128#usize) × Array U64 8#usize => blocks.length-p.1.i)
    (inv := fun p => p.1.slice = blocks ∧ p.1.i ≤ blocks.length ∧
      slhdsa.S512.wv p.2.val = fold512 (slhdsa.S512.wv st.val) (blocks.val.take p.1.i))
  · rintro ⟨it,state⟩ ⟨slice,bound,prev⟩
    simp only at slice bound prev
    by_cases more : it.i < blocks.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some blocks.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      step with block512 state it next _ get as ⟨flow,out,eq,hash⟩
      subst flow
      simp only
      refine ⟨slice,by change it.i+1 ≤ blocks.length; omega,?_,by change blocks.length-(it.i+1) < blocks.length-it.i; omega⟩
      rw [hash,prev]
      rw [List.take_succ_eq_append_getElem more]
      simp only [fold512,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length]
      simp only
      unfold StreamScalarRust.sha512.stream.scalar_loop0.body
      rw [doneIt]
      simp only [bind_ok,step_simps]
      simpa [List.take_of_length_le (show blocks.val.length ≤ it.i by exact Nat.le_of_not_gt more)] using prev
  · exact ⟨rfl,Nat.zero_le _,by simp [fold512]⟩

end slhdsa.X86.Stream
