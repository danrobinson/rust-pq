import Parallel.ForsMetaScalar
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsMetadata
open ShakeBatch

theorem group_loop (choices : alloc.vec.Vec U32) (a j sub : U32) (start first active chunks : Usize)
    (old : Table) (ha : a.val≤14) (below : j.val<a.val) (count : choices.length≤35)
    (range : first.val+active.val≤choices.length) (digits : ∀ t<choices.length, choices.val[t]!.val<2^a.val)
    (cv : chunks.val=2^(j.val-sub.val)) (space : start.val+active.val*chunks.val≤Usize.max)
    (capacity : old.length+active.val≤Usize.max) :
    meta_group_loop ⟨0#usize,active⟩ choices a j sub first old chunks start ⦃ out =>
      Emitted choices a j sub first.val active.val start.val old out ⦄ := by
  unfold meta_group_loop
  apply range_fold (meta_group_loop.body choices a j sub first chunks start) active old
    (fun l out => Emitted choices a j sub first.val l start.val old out) (by simp [Emitted])
  · intro it cur stop live prev
    have length := prev.1
    have small : first.val+it.start.val<choices.length := by omega
    have mx : 2^32-1≤Usize.max := by agrind
    have target := Nat.mul_le_mul_right chunks.val (show it.start.val≤active.val by omega)
    unfold meta_group_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,last⟩
    simp only [tag,lift,bind_ok]
    step as ⟨idx,iv⟩
    let t := UScalar.cast .U32 idx
    have cast : t.val=idx.val := cast_u32_usize_val _ (by omega)
    have source := U32.cast_Usize_val_eq t
    step as ⟨d,dv⟩
    step with offset t a j d dv (by omega) ha as ⟨base,bv⟩
    step as ⟨digit,read⟩
    have rd : digit=choices.val[t.val]! := by rw [read,←getElem!_pos,source]
    have l : t.val<choices.length := by omega
    obtain ⟨root,rootRun,rv⟩ := spec_imp_exists (root_value choices a j t.val base digit ha below count l (digits _ l) bv rd)
    have joined {α} (f : U32 → Result α) : (do let high ← digit >>> j;let r ← base+(high^^^1#u32);f r)=f root := by
      simpa only [Std.bind_assoc,bind_tc_eq,lift,bind_ok] using congrArg (fun v : Result U32 => v >>= f) rootRun
    rw [joined]
    step as ⟨off,ov⟩
    step as ⟨slot,sv⟩
    step as ⟨out,push⟩
    refine ⟨next,out,rfl,last.trans stop,inc,?_⟩
    rw [inc]
    apply append_record choices a j sub first.val it.start.val start.val old cur out ⟨t,j,root,sub,slot,chunks⟩ prev _ push
    simp only [Record,cast,iv,rv,sv,ov,cv,true_and,and_self]
  · intro it cur last stop
    obtain ⟨_,no⟩ := ForsDriver.range_done it _ stop last
    simp [meta_group_loop.body,no]

theorem group (choices : alloc.vec.Vec U32) (a j sub : U32) (start first active : Usize)
    (old : Table) (ha : a.val≤14) (below : j.val<a.val) (lower : sub.val<j.val) (count : choices.length≤35)
    (range : first.val+active.val≤choices.length) (digits : ∀ t<choices.length, choices.val[t]!.val<2^a.val)
    (space : start.val+active.val*2^(j.val-sub.val)≤Usize.max) (capacity : old.length+active.val≤Usize.max) :
    meta_group choices a j sub start first active old ⦃ next out =>
      next.val=start.val+active.val*2^(j.val-sub.val) ∧ Emitted choices a j sub first.val active.val start.val old out ⦄ := by
  unfold meta_group
  step as ⟨d,dv⟩
  step with chunk_count j sub d dv (by omega) as ⟨n,nv⟩
  have fit : active.val*n.val≤Usize.max := by rw [nv];omega
  have room : start.val+active.val*n.val≤Usize.max := by rwa [nv]
  step as ⟨count1,cv⟩
  step as ⟨next,size⟩
  step with group_loop choices a j sub start first active n old ha below count range digits nv room capacity as ⟨out,post⟩
  exact ⟨by rw [size,cv,nv],post⟩
end slhdsa.ForsMetadata
