import Parallel.ForestPackProgram
import Parallel.CacheTicketSignature
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForestPack
set_option maxHeartbeats 1000000

theorem pack_spec {N : Usize} (p : params.Params) (hp : PN p N) (cells : alloc.vec.Vec (Option (Array U8 N)))
    (field : Nat → Spec.Bytes) (published : ∀ j<cells.length, ∃ row, cells.val[j]! = some row ∧ bytes row.val=field j)
    (fits : cells.length*N.val≤Usize.max) :
    pack_fors p cells ⦃ out => bytes out.val=(List.range cells.length).flatMap field ⦄ := by
  unfold pack_fors
  step with fors_sig_bytes_spec p hp.valid as ⟨cap,_,_⟩
  simp only [core.slice.Slice.iter,bind_ok]
  unfold pack_fors_loop
  apply loop.spec_decr_nat (measure := fun q : core.slice.iter.Iter (Option (Array U8 N)) × alloc.vec.Vec U8 => cells.length-q.1.i)
    (inv := fun q => q.1.slice=cells.deref ∧ q.1.i≤cells.length ∧ q.2.length=q.1.i*N.val ∧
      bytes q.2.val=(List.range q.1.i).flatMap field)
  · rintro ⟨it,cur⟩ ⟨slice,le,len,prior⟩
    simp only at slice le len prior ⊢
    unfold pack_fors_loop.body
    by_cases more : it.i<cells.length
    · obtain ⟨row,cell,eq⟩ := published it.i more
      let next := {it with i:=it.i+1}
      have read : core.slice.iter.IteratorSliceIter.next it=ok (some (some row),next) := by
        have inRange : it.i < it.slice.len.val := by simpa [slice] using more
        have hv : it.i<cells.val.length := more
        have base : core.slice.iter.IteratorSliceIter.next it=ok (some cells.val[it.i],next) := by
          simp [core.slice.iter.IteratorSliceIter.next,inRange,next,slice,more,Slice.length,vec_deref_val]
        rw [←getElem!_pos cells.val it.i hv,cell] at base
        exact base
      simp only [read,bind_ok,ParallelSignJoin.readCell,core.option.Option.expect,ofOption,lift]
      have capacity := Nat.mul_le_mul_right N.val more
      rw [Nat.succ_mul] at capacity
      step with util_extend_from_slice_u8_spec cur row.to_slice (by simpa [len] using capacity.trans fits) as ⟨out,saved,size⟩
      refine ⟨slice,by change it.i+1≤cells.length;omega,?_,?_,by change cells.length-(it.i+1)<cells.length-it.i;omega⟩
      · simp [size,len,next,Nat.succ_mul]
      · simp [saved,bytes_append,Array.val_to_slice,prior,eq,next,List.range_succ]
    · have read : core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length]
      simp only [read,step_simps]
      exact (show it.i=cells.length by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,by change 0=0*N.val;simp,rfl⟩

theorem pack_fips {N : Usize} (p : params.Params) (hp : PN p N) (cells : alloc.vec.Vec (Option (Array U8 N)))
    (md sk pk : Spec.Bytes) (a : Spec.Adrs) (count : cells.length=p.k.val*(1+p.a.val))
    (published : ∀ j<cells.length, ∃ row, cells.val[j]! = some row ∧
      bytes row.val=(ParallelCached.forsRows (Shake.params p) md sk pk a)[j]!) :
    pack_fors p cells ⦃ out => bytes out.val=Spec.forsSign (Shake.params p) md sk pk a ⦄ := by
  let rows := ParallelCached.forsRows (Shake.params p) md sk pk a
  have size : rows.length=cells.length := (ParallelCached.fors_length _ _ _ _ _).trans count.symm
  have indices : (List.range cells.length).map (fun j => rows[j]!)=rows := by
    apply List.ext_getElem
    · simp [size]
    · intro i hi hj
      have h : i<cells.length := size ▸ hj
      simp [List.getElem?_eq_getElem hj]
  have fits : cells.length*N.val≤Usize.max := by
    have k : p.k.val≤35 := hp.valid.k_le
    have a : p.a.val≤14 := hp.valid.a_le
    have cap := Nat.mul_le_mul (Nat.mul_le_mul k (show 1+p.a.val≤15 by omega)) hp.le32
    rw [count];scalar_tac
  apply WP.spec_mono (pack_spec p hp cells (fun j => rows[j]!) published fits)
  intro out eq
  rw [eq,←ParallelCached.fors_bytes]
  change (List.range cells.length).flatMap (fun j => rows[j]!)=rows.flatten
  simpa only [List.flatMap_def] using congrArg List.flatten indices

end slhdsa.ParallelForestPack
