import Koriented.Fips
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result ControlFlow
open Spec.Keccak
namespace slhdsa.Oriented
set_option maxHeartbeats 2500000
open KorientedRust.shake256

theorem rotateInverse (x : Lane) (r : Nat) : (x.rotateRight r).rotateLeft r = x := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split <;> split <;> (first | congr 1 <;> omega | omega)

private theorem wordAt (a : Array U64 25#usize) (i : Nat) (hi : i < 25) :
    (Keccak.words a)[i]! = a.val[i]!.bv := by simp [Keccak.words,getElem!_pos,hi]

theorem start (a : Array U64 25#usize) :
    core.array.from_fn 25#usize oriented.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 a
      ⦃ out => decode out = Keccak.words a ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 25#usize _ _
    (fun i (x : U64) => x.bv.rotateLeft (oriented.OFF.val[i]!.val) = a.val[i]!.bv) ?_)
  · intro out h
    apply ext25 _ _ (by simp [decode]) (by simp [Keccak.words])
    intro i hi
    rw [wordAt _ _ hi]
    unfold decode
    rw [ofFnAt _ _ hi]
    simpa only [Array.getElem!_Nat_eq] using h i hi
  intro k hk
  unfold oriented.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  simp only [oriented.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,lift,bind_ok]
  step*
  simp only [getElem!_pos a.val k.val (show k.val < a.val.length by simpa using hk),
    getElem!_pos oriented.OFF.val k.val (show k.val < oriented.OFF.val.length by simpa using hk)]
  rw [i_post,i1_post]
  exact rotateInverse _ _

theorem rounds (a : Array U64 25#usize) (keys : Slice U64) :
    oriented.permute_loop0 ⟨keys,0⟩ a ⦃ out => decode out = (keys.val.map (·.bv)).foldl round (decode a) ⦄ := by
  unfold oriented.permute_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter U64 × Array U64 25#usize) => keys.length-p.1.i)
    (inv := fun p => p.1.slice = keys ∧ p.1.i ≤ keys.length ∧
      decode p.2 = ((keys.val.take p.1.i).map (·.bv)).foldl round (decode a))
  · rintro ⟨it,state⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior ⊢
    unfold oriented.permute_loop0.body
    by_cases more : it.i < keys.length
    · let next := {it with i := it.i+1}
      have index : it.i < it.slice.len.val := by simpa [slice] using more
      have get : core.slice.iter.IteratorSliceIter.next it = ok (some keys.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,index,next,slice,more,Slice.length]
      rw [get]
      simp only [bind_ok]
      step with round_fips state _ as ⟨out,post⟩
      refine ⟨slice,by change it.i+1 ≤ keys.length; omega,?_,by change keys.length-(it.i+1) < keys.length-it.i; omega⟩
      rw [post,prior]
      change _ = (((keys.val.take (it.i+1)).map _).foldl _ _)
      rw [List.take_succ_eq_append_getElem more,List.map_append,List.foldl_append]
      rfl
    · have doneIt : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length] at *
      rw [doneIt]
      simp only [step_simps]
      simpa [show it.i=keys.length by omega,Slice.length] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp⟩


theorem finish (a state : Array U64 25#usize) :
    oriented.permute_loop1 ⟨0#usize,25#usize⟩ state a ⦃ out => Keccak.words out = decode a ⦄ := by
  unfold oriented.permute_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 25#usize) => 25 - p.1.start.val)
    (inv := fun p => p.1.end = 25#usize ∧ p.1.start.val ≤ 25 ∧
      ∀ j, j < p.1.start.val → p.2.val[j]!.bv = (decode a)[j]!)
  · rintro ⟨it,state⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    simp only at *
    unfold oriented.permute_loop1.body
    by_cases more : it.start.val < 25
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      rw [get]
      simp only [bind_ok,lift]
      step as ⟨x,hx⟩
      step as ⟨off,hoff⟩
      step as ⟨out,hout⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro j hj
      have hj25 : j < 25 := by omega
      rw [hout, Array.set_val_eq, getElem!_pos _ _ (by simp; omega),List.getElem_set]
      split
      · subst j
        unfold decode
        rw [ofFnAt _ _ more]
        simp only [getElem!_pos a.val it.start.val (by simpa using more),
          getElem!_pos oriented.OFF.val it.start.val (by simpa using more)]
        rw [hx,hoff]
        rfl
      · rw [← getElem!_eq state.val j (by simpa using hj25)]
        exact prior _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.not_lt.mp more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      apply ext25 _ _ (by simp [Keccak.words]) (by simp [decode])
      intro j hj
      rw [wordAt _ _ hj]
      exact prior j (by omega)
  · exact ⟨rfl,Nat.zero_le _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

theorem permute_fips (state : Array U64 25#usize) :
    oriented.permute state ⦃ out => Keccak.words out = permute (Keccak.words state) ⦄ := by
  unfold oriented.permute
  step with start state as ⟨a,ha⟩
  simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  step with rounds a _ as ⟨r,hr⟩
  step with finish r state as ⟨out,hout⟩
  rw [hout,hr,ha]
  have constants : KorientedRust.shake256.RC.val.map (·.bv) = rc.toList := by
    unfold KorientedRust.shake256.RC rc
    rfl
  simp only [Slice.from_val]
  change (KorientedRust.shake256.RC.val.map (·.bv)).foldl round _ = _
  rw [constants]
  rfl

end slhdsa.Oriented
