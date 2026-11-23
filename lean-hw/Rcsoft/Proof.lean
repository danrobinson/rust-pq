import Rcsoft.Rounds
import Armstream.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.RcSoftProof
open Spec.SHA512 RcSoft.sha512.soft.unroll X86.Stream

set_option maxHeartbeats 2000000 in
theorem block_spec (st : Array U64 8#usize) (block : Array U8 128#usize) :
    compress_block st block ⦃ out => S512.wv out.val = Spec.SHA512.compress (S512.wv st.val) (bytes block.val) ⦄ := by
  unfold compress_block
  step with words_spec block as ⟨words,hwords⟩
  step*
  step with round_loop (bytes block.val) (S512.st8 (a,b,c,d,e,f,g,h)) as ⟨a1,b1,c1,d1,e1,f1,g1,h1,rounds⟩
  · exact ⟨rfl, by change 0 ≤ 80; decide, ring_init _ _ hwords, rfl⟩
  step*
  have hs : ∀ j (hj : j < 8), (S512.wv st.val)[j]! = (st.val[j]'(by scalar_tac)).bv :=
    fun j hj => S512.wv_getElem! _ _ _
  simp only [Spec.SHA512.compress]
  rw [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide),
    hs 4 (by decide), hs 5 (by decide), hs 6 (by decide), hs 7 (by decide)]
  simp only [S512.st8, a_post,b_post,c_post,d_post,e_post,f_post,g_post,h_post] at rounds
  rw [← rounds]
  simp [S512.wv, *]
  apply List.ext_getElem
  · simp
  · intro j _ hj
    have hj8 : j < 8 := by simpa using hj
    interval_cases j <;> simp

theorem execute_is_fips (st : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :
    RcSoft.sha512.soft.unroll.compress st blocks ⦃ out =>
      S512.wv out.val = fold512 (S512.wv st.val) blocks.val ⦄ := by
  unfold RcSoft.sha512.soft.unroll.compress
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  unfold compress_loop
  apply loop.spec_decr_nat
    (measure := fun p : core.slice.iter.Iter (Array U8 128#usize) × Array U64 8#usize => blocks.length-p.1.i)
    (inv := fun p => p.1.slice = blocks ∧ p.1.i ≤ blocks.length ∧
      S512.wv p.2.val = fold512 (S512.wv st.val) (blocks.val.take p.1.i))
  · rintro ⟨it,state⟩ ⟨slice,bound,prev⟩
    simp only at slice bound prev
    simp only [compress_loop.body]
    by_cases more : it.i < blocks.length
    · let next := {it with i := it.i+1}
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some blocks.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,next,slice,more]
      rw [get]; simp only [bind_ok]
      step with block_spec as ⟨out,hash⟩
      refine ⟨slice,by change it.i+1 ≤ blocks.length; omega,?_,by change blocks.length-(it.i+1) < blocks.length-it.i; omega⟩
      rw [hash,prev]
      change _ = fold512 _ (blocks.val.take (it.i+1))
      rw [List.take_succ_eq_append_getElem more]
      simp only [fold512,List.foldl_append,List.foldl_cons,List.foldl_nil]
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more]
      rw [doneIt]
      simp only [bind_ok,step_simps]
      simpa [List.take_of_length_le (show blocks.val.length ≤ it.i by exact Nat.le_of_not_gt more)] using prev
  · exact ⟨rfl,Nat.zero_le _,by simp [fold512]⟩

theorem armstream_contract (st : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :
    RcSoft.sha512.soft.unroll.compress st blocks ⦃ out =>
      ArmStreamRust.sha2.sha512.compress512 st blocks ⦃ modeled => modeled = out ⦄ ⦄ := by
  apply WP.spec_mono (execute_is_fips st blocks)
  intro out actual
  apply WP.spec_mono (PlatformStream.bulk512 st blocks)
  intro modeled spec
  apply Aeneas.Std.Array.ext
  have eq := spec.trans actual.symm
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have same := congrArg (fun xs : List Word => xs[j]!) eq
    simp only [S512.wv_getElem! _ _ hj, S512.wv_getElem! _ _ hk] at same
    exact congrArg (@UScalar.mk .U64) same

end slhdsa.RcSoftProof
