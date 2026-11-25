import Parallel.SignJoinProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelSignJoin
open ShakeBatch

def through {α} (f : Nat → List α) (i : Nat) := (List.range i).flatMap f

theorem through_succ {α} (f : Nat → List α) (i : Nat) :
    through f (i+1) = through f i ++ f i := by simp [through,List.range_succ]

theorem length_mono {α} (f : Nat → List α) {i j : Nat} (h : i≤j) :
    (through f i).length ≤ (through f j).length := by
  induction h with
  | refl => rfl
  | step le ih => rw [through_succ,List.length_append]; omega

def authRows {N : Usize} (v : alloc.vec.Vec (Array U8 N)) (hp j h : Nat) := v.val[j*hp+h]!.val

theorem auth_copy {N : Usize} (hp j : Usize) (v : alloc.vec.Vec (Array U8 N)) (init : alloc.vec.Vec U8)
    (index : (j.val+1)*hp.val ≤ v.length)
    (fit : init.length + (through (authRows v hp.val j.val) hp.val).length ≤ Usize.max) :
    run_loop0_loop0 ⟨0#usize,hp⟩ hp v init j ⦃ out => out.val=init.val ++ through (authRows v hp.val j.val) hp.val ⦄ := by
  unfold run_loop0_loop0
  apply range_fold (run_loop0_loop0.body hp v j) hp init (fun i st => st.val=init.val ++ through (authRows v hp.val j.val) i)
  · simp [through]
  · intro it st stop live prev
    unfold run_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    have cap : v.length ≤ Usize.max := by simp
    rw [Nat.add_mul,one_mul] at index
    step as ⟨pos,mul⟩
    step as ⟨k,add⟩
    step as ⟨row,read⟩
    simp only [lift,bind_ok]
    have size := length_mono (authRows v hp.val j.val) (Nat.succ_le_of_lt live)
    rw [through_succ,List.length_append] at size
    have cell : row.val=authRows v hp.val j.val it.start.val := by
      rw [read,← getElem!_pos]; simp [authRows,add,mul]
    have sizeFit : st.length+row.val.length ≤ Usize.max := by
      change st.val.length+row.val.length ≤ _
      rw [cell,prev,List.length_append]
      change init.val.length + _ ≤ _ at fit
      omega
    step with util_extend_from_slice_u8_spec st row.to_slice (by simpa using sizeFit) as ⟨out,write,_⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    rw [write,prev,inc,through_succ,List.append_assoc]
    simpa using cell
  · intro it st last stop
    unfold run_loop0_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

def wotsRows (v : alloc.vec.Vec (Option (alloc.vec.Vec U8))) (j : Nat) : List U8 :=
  (v.val[j]!.map (fun row => row.val)).getD []

def layers {N : Usize} (auth : alloc.vec.Vec (Array U8 N)) (wots : alloc.vec.Vec (Option (alloc.vec.Vec U8)))
    (hp j : Nat) := wotsRows wots j ++ through (authRows auth hp j) hp

theorem layer_copy {N : Usize} (hp d : Usize) (v : alloc.vec.Vec (Array U8 N))
    (wots : alloc.vec.Vec (Option (alloc.vec.Vec U8))) (init : alloc.vec.Vec U8)
    (authFit : d.val*hp.val ≤ v.length) (wotsFit : d.val ≤ wots.length)
    (present : ∀ j < d.val, ∃ row, wots.val[j]! = some row)
    (fit : init.length + (through (layers v wots hp.val) d.val).length ≤ Usize.max) :
    run_loop0 ⟨0#usize,d⟩ hp wots v init ⦃ out => out.val=init.val ++ through (layers v wots hp.val) d.val ⦄ := by
  unfold run_loop0
  apply range_fold (run_loop0.body hp wots v) d init (fun i st => st.val=init.val ++ through (layers v wots hp.val) i)
  · simp [through]
  · intro it st stop live prev
    unfold run_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨slot,read⟩
    obtain ⟨row,has⟩ := present _ live
    rw [←getElem!_pos] at read
    simp only [read,has,readCell,core.option.Option.expect,ofOption,bind_ok]
    have rowEq : wotsRows wots it.start.val=row.val := by simp [wotsRows,has]
    have size := length_mono (layers v wots hp.val) (Nat.succ_le_of_lt live)
    rw [through_succ,layers,List.length_append,List.length_append,rowEq] at size
    have sizeFit : st.length + row.length + (through (authRows v hp.val it.start.val) hp.val).length ≤ Usize.max := by
      change st.val.length+row.val.length+_ ≤ _
      rw [prev,List.length_append]
      change init.val.length+_ ≤ _ at fit
      omega
    have rl : row.deref.length=row.length := by change row.deref.val.length=row.val.length; rw [vec_deref_val]
    step with util_extend_from_slice_u8_spec st row.deref (by rw [rl]; omega) as ⟨st',added,newLen⟩
    have domain := (Nat.mul_le_mul_right hp.val (Nat.succ_le_of_lt live)).trans authFit
    step with auth_copy hp it.start v st' domain (by rw [newLen,rl];exact sizeFit) as ⟨out,stored⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    simp [stored,added,prev,vec_deref_val,inc,through_succ,layers,rowEq,List.append_assoc]
  · intro it st last stop
    unfold run_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.ParallelSignJoin
