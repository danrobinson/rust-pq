import Cachepath.WotsFusedProgram
import Cachepath.FusedStream
import Shakebatch.Range

open Aeneas Aeneas.Std Result ControlFlow slhdsa.ShakeBatch
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open Spec.Keccak
set_option linter.concreteInstances false
variable [machine : Machine]

private def xorCell (s : Matrix machine.width) (r j : Usize) (w : U64) : Result (Matrix machine.width) := do
  let row ← Array.index_usize s r
  let old ← Array.index_usize row j
  let v ← lift (old ^^^ w)
  let (row,back) ← Array.index_mut_usize s r
  let row ← Array.update row j v
  ok (back row)

private theorem xorCell_bind {α : Type} (s : Matrix machine.width) (r j : Usize) (w : U64)
    (k : Matrix machine.width → Result α) :
    (xorCell s r j w >>= k) = (do
      let row ← Array.index_usize s r
      let old ← Array.index_usize row j
      let v ← lift (old ^^^ w)
      let (row,back) ← Array.index_mut_usize s r
      let row ← Array.update row j v
      k (back row)) := by
  simp only [xorCell,uncurry,bind_tc_eq,Std.bind_assoc,bind_ok]
  repeat' congr 1

private theorem xorCell_spec (s : Matrix machine.width) (r j : Usize) (w : U64)
    (hr : r.val < 25) (hj : j.val < machine.width.val) :
    xorCell s r j w ⦃ out => ∀ l < machine.width.val, ShakeBatch.lane out l =
      if l=j.val then (ShakeBatch.lane s l).setIfInBounds r.val ((ShakeBatch.lane s l)[r.val]! ^^^ w.bv) else ShakeBatch.lane s l ⦄ := by
  unfold xorCell
  step as ⟨row,read⟩
  step as ⟨old,oldEq⟩
  simp only [lift,bind_ok]
  step as ⟨_,back,rowRead,write⟩
  step as ⟨_,update⟩
  intro l hl
  rw [write,update,rowRead,← getElem!_pos]
  apply ext25 _ _ (by simp [ShakeBatch.lane]) (by split <;> simp [ShakeBatch.lane])
  intro k hk
  rw [show (ShakeBatch.lane _ l)[k]! = _ from ofFnAt _ k hk,cell_write _ _ _ _ hr hj]
  rw [oldEq,read,← getElem!_pos,← getElem!_pos]
  by_cases eq : l=j.val
  · subst l
    simp only [and_true,ite_true]
    rw [setAt (ShakeBatch.lane s _) _ k _ (by simpa [ShakeBatch.lane] using hk)]
    simp only [ShakeBatch.lane,ofFnAt _ k hk,ofFnAt _ _ hr,cell]
    by_cases same : k=r.val <;> simp only [same,ite_true,ite_false] <;> first | rfl | simp [Ne.symm same]
  · simp [eq,ShakeBatch.lane,ofFnAt _ _ hk]

private theorem sweep (body : Range → Matrix machine.width → Result (ControlFlow (Range × Matrix machine.width) (Matrix machine.width)))
    (init : Matrix machine.width) (f : Nat → State → State)
    (advance : ∀ it s, it.end = machine.width → it.start.val < machine.width.val →
      body it s ⦃ r => ∃ next out, r=cont (next,out) ∧ next.end=machine.width ∧
        next.start.val=it.start.val+1 ∧ ∀ l < machine.width.val,
        ShakeBatch.lane out l = if l=it.start.val then f l (ShakeBatch.lane s l) else ShakeBatch.lane s l ⦄)
    (doneAt : ∀ it s, it.start.val = machine.width.val → it.end = machine.width → body it s=ok (done s)) :
    loop (fun q : Range × Matrix machine.width => body q.1 q.2) (⟨0#usize,machine.width⟩,init)
      ⦃ out => ∀ l < machine.width.val, ShakeBatch.lane out l = f l (ShakeBatch.lane init l) ⦄ := by
  apply WP.spec_mono (range_fold body machine.width init (fun n s => ∀ l < machine.width.val,
      ShakeBatch.lane s l = if l<n then f l (ShakeBatch.lane init l) else ShakeBatch.lane init l) (by simp) ?_ doneAt)
  · intro s h l hl; simpa [hl] using h l hl
  · intro it s he live old
    apply WP.spec_mono (advance it s he live)
    rintro _ ⟨next,out,rfl,stop,inc,changed⟩
    refine ⟨next,out,rfl,stop,inc,?_⟩
    intro l hl
    rw [changed l hl,old l hl,inc]
    split <;> split <;> simp_all <;> omega

theorem absorb_row (s : Matrix machine.width) (pos : Usize) (word : Array U64 machine.width) (hr : pos.val<17) :
    generate_loop0_loop1_loop0 ⟨0#usize,machine.width⟩ s pos word ⦃ out =>
    ∀ l < machine.width.val, ShakeBatch.lane out l =
      (ShakeBatch.lane s l).setIfInBounds pos.val ((ShakeBatch.lane s l)[pos.val]! ^^^ word.val[l]!.bv) ⦄ := by
  unfold generate_loop0_loop1_loop0
  apply sweep (generate_loop0_loop1_loop0.body pos word) s
    (fun l a => a.setIfInBounds pos.val (a[pos.val]! ^^^ word.val[l]!.bv))
  · intro it state stop live
    unfold generate_loop0_loop1_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,ho,hn,he⟩
    simp only [ho,bind_ok]
    step as ⟨w,read⟩
    rw [← xorCell_bind state pos it.start w (fun out => ok (cont (next,out)))]
    step with xorCell_spec state pos it.start w (by omega) live as ⟨out,eq⟩
    refine ⟨next,out,rfl,he.trans stop,hn,?_⟩
    intro l hl
    rw [eq l hl,read,← getElem!_pos]
    split <;> simp_all
  · intro it state last stop
    unfold generate_loop0_loop1_loop0.body
    obtain ⟨⟨_,_⟩,next,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [next,ho]

/-- Each SIMD column absorbs the same number of words from its own chain tip. -/
theorem absorb_rows (input : Slice (Array U64 machine.width)) (s : Matrix machine.width)
    (pos : Usize) (hr : pos.val<17) (permutes : PermutationCorrect) :
    generate_loop0_loop1 ⟨input,0⟩ s pos ⦃ out =>
      out.2.val < 17 ∧ ∀ l < machine.width.val, (ShakeBatch.lane out.1 l,out.2.val) =
        input.val.foldl (fun acc row => FusedStream.absorb acc row.val[l]!.bv) (ShakeBatch.lane s l,pos.val) ⦄ := by
  unfold generate_loop0_loop1
  apply loop.spec_decr_nat (measure := fun q => input.length-q.1.i)
    (inv := fun q => q.1.slice=input ∧ q.1.i ≤ input.length ∧ q.2.2.val < 17 ∧
      ∀ l < machine.width.val, (ShakeBatch.lane q.2.1 l,q.2.2.val) =
        (input.val.take q.1.i).foldl (fun acc row => FusedStream.absorb acc row.val[l]!.bv)
          (ShakeBatch.lane s l,pos.val))
  · rintro ⟨⟨slice,i⟩,state,atPos⟩ ⟨rfl,le,rate,old⟩
    simp only at le rate old
    unfold generate_loop0_loop1.body core.slice.iter.IteratorSliceIter.next
    by_cases more : i < slice.length
    · have live : i < slice.len.val := by simpa using more
      simp only [dite_eq_left live,bind_ok]
      step with absorb_row state atPos slice[i] rate as ⟨updated,eq⟩
      step as ⟨next,inc⟩
      have wordEq (l : Nat) (hl : l<machine.width.val) :
          (slice.val.take (i+1)).foldl (fun acc (row : Array U64 machine.width) => FusedStream.absorb acc row.val[l]!.bv)
              (ShakeBatch.lane s l,pos.val) =
          FusedStream.absorb (ShakeBatch.lane state l,atPos.val) (slice[i].val[l]!.bv) := by
        rw [List.take_succ_eq_append_getElem more,List.foldl_append,← old l hl]; rfl
      by_cases boundary : next = 17#usize
      · simp only [boundary,ite_true]
        step with permutes updated as ⟨mixed,permuted⟩
        refine ⟨by omega,by decide,?_,by omega⟩
        intro l hl
        rw [wordEq l hl,permuted l hl,eq l hl]
        have last : atPos.val=16 := by rw [boundary] at inc; scalar_tac
        simp [FusedStream.absorb,last]
      · simp only [boundary,ite_false,step_simps]
        have last : atPos.val≠16 := by intro e; apply boundary; apply UScalar.eq_of_val_eq; scalar_tac
        refine ⟨by omega,by omega,?_,by omega⟩
        intro l hl
        rw [wordEq l hl,eq l hl]
        simp [FusedStream.absorb,last,inc]
    · have dead : ¬i < slice.len.val := by simpa using more
      simp only [dite_eq_right dead,step_simps]
      exact ⟨rate,fun l hl => by simpa [show i=slice.length by omega] using old l hl⟩
  · simpa using hr

theorem absorb_tip_rows (input : Slice (Array U64 machine.width)) (s : Matrix machine.width)
    (pos : Usize) (hr : pos.val<17) (permutes : PermutationCorrect)
    (tip : Nat → Spec.Bytes) (length : ∀ l < machine.width.val, (tip l).length = 8*input.length)
    (words : ∀ l < machine.width.val, ∀ i < input.length,
      input.val[i]!.val[l]!.bv = messageWord (tip l) i) :
    generate_loop0_loop1 ⟨input,0⟩ s pos ⦃ out =>
      out.2.val < 17 ∧ ∀ l < machine.width.val, (ShakeBatch.lane out.1 l,8*out.2.val) =
        (tip l).foldl feed (ShakeBatch.lane s l,8*pos.val) ⦄ := by
  apply WP.spec_mono (absorb_rows input s pos hr permutes)
  rintro ⟨out,next⟩ ⟨rate,absorbed⟩
  refine ⟨rate,?_⟩
  intro l hl
  have eq : input.val.map (fun row => row.val[l]!.bv) =
      (List.range input.length).map (messageWord (tip l)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_map,List.getElem_map,List.getElem_range,← getElem!_pos]
      exact words l hl i (by simpa using hi)
  have step := absorbed l hl
  have foldEq := congrArg (fun ws => ws.foldl FusedStream.absorb (ShakeBatch.lane s l,pos.val)) eq
  simp only [List.foldl_map] at foldEq
  rw [foldEq] at step
  have ref := FusedStream.absorb_tip (tip l) input.length (length l hl) (ShakeBatch.lane s l)
    (by simp [ShakeBatch.lane]) pos.val hr
  rw [← ref,← step]

def padWords (pos : Nat) (a : State) : State :=
  let tagged := a.setIfInBounds pos (a[pos]! ^^^ 0x1f)
  tagged.setIfInBounds 16 (tagged[16]! ^^^ (1 <<< 63))

theorem pad_rows (s : Matrix machine.width) (pos : Usize) (hr : pos.val<17) :
    generate_loop1 ⟨0#usize,machine.width⟩ s pos ⦃ out =>
    ∀ l < machine.width.val, ShakeBatch.lane out l = padWords pos.val (ShakeBatch.lane s l) ⦄ := by
  unfold generate_loop1
  apply sweep (generate_loop1.body pos) s (fun _ a => padWords pos.val a)
  · intro it state stop live
    unfold generate_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,ho,hn,he⟩
    have shift : (1#u64 <<< 63#i32) = ok 9223372036854775808#u64 := by rfl
    simp only [ho,shift,bind_ok]
    simp_rw [← xorCell_bind _ 16#usize it.start 9223372036854775808#u64 (fun u => ok (cont (next,u)))]
    rw [← xorCell_bind state pos it.start 31#u64 (fun t =>
        xorCell t 16#usize it.start 9223372036854775808#u64 >>= fun u => ok (cont (next,u)))]
    step with xorCell_spec state pos it.start 31#u64 (by omega) live as ⟨first,tag⟩
    step with xorCell_spec first 16#usize it.start 9223372036854775808#u64 (by decide) live as ⟨last,bit⟩
    refine ⟨next,last,rfl,he.trans stop,hn,?_⟩
    intro l hl
    rw [bit l hl,tag l hl]
    by_cases same : l=it.start.val <;> simp only [same,ite_true,ite_false,padWords] <;> rfl
  · intro it state last stop
    unfold generate_loop1.body
    obtain ⟨⟨_,_⟩,next,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [next,ho]

theorem finish_rows (s : Matrix machine.width) (pos : Usize) (hr : pos.val<17) (permutes : PermutationCorrect) :
    (do let padded ← generate_loop1 ⟨0#usize,machine.width⟩ s pos
        machine.permute padded) ⦃ out => ∀ l < machine.width.val,
          ShakeBatch.lane out l = finalize (ShakeBatch.lane s l,8*pos.val) ⦄ := by
  step with pad_rows s pos hr as ⟨padded,tag⟩
  apply WP.spec_mono (permutes padded)
  intro out eq l hl
  rw [eq l hl,tag l hl]
  exact FusedStream.finish_eq _ _

end slhdsa.cache.builder.nativeShake.Vector.Fused
