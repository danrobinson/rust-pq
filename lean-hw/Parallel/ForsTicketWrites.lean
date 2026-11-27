import Parallel.ForsTicketProgram
import ForsDriver.ForsIndices
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForsTicket
open ShakeBatch

theorem direct_writes {N : Usize} (active : Usize) (stride first : Usize) (j : U32)
    (rows : Array (Array U8 N) 3#usize) (journal : Array (Usize × Array U8 N) 3#usize)
    (width : active.val≤3) (valid : first.val+active.val≤35)
    (fit : ∀ l<active.val, (first.val+l)*stride.val+1+j.val ≤ Usize.max) :
    direct_ticket_loop ⟨0#usize,active⟩ stride first j rows journal ⦃ out => ∀ l<active.val,
      out.val[l]!.1.val=(first.val+l)*stride.val+1+j.val ∧ out.val[l]!.2=rows.val[l]! ⦄ := by
  unfold direct_ticket_loop
  apply range_fold (direct_ticket_loop.body stride first j rows) active journal
    (fun n out => ∀ l<n, out.val[l]!.1.val=(first.val+l)*stride.val+1+j.val ∧ out.val[l]!.2=rows.val[l]!) (by simp)
  · intro it current stop live prior
    have lim := fit it.start.val live
    have addFit : first.val+it.start.val≤Usize.max := by
      scalar_tac
    unfold direct_ticket_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag,lift,bind_ok]
    step as ⟨idx,iv⟩
    step as ⟨base,bv⟩
    step as ⟨off,ov⟩
    step as ⟨slot,sv⟩
    step as ⟨row,read⟩
    step as ⟨out,put⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    intro l hl
    rw [put,Array.set_val_eq]
    by_cases eq : l=it.start.val
    · subst l
      rw [setSame _ _ _ (by simp;omega)]
      exact ⟨by rw [sv,ov,bv,iv,U32.cast_Usize_val_eq],by rw [read,←getElem!_pos]⟩
    · rw [setOther _ _ _ _ (Ne.symm eq)]
      exact prior l (by omega)
  · intro it rows last stop
    obtain ⟨n,no⟩ := ForsDriver.range_done it _ stop last
    simp [direct_ticket_loop.body,no]

theorem split_writes {N : Usize} (active : Usize) (chunk : U32) (base chunks : Usize)
    (rows : Array (Array U8 N) 3#usize) (journal : Array (Usize × Array U8 N) 3#usize)
    (width : active.val≤3)
    (fit : ∀ l<active.val, base.val+l*chunks.val+chunk.val ≤ Usize.max) :
    split_ticket_loop ⟨0#usize,active⟩ chunk base chunks rows journal ⦃ out => ∀ l<active.val,
      out.val[l]!.1.val=base.val+l*chunks.val+chunk.val ∧ out.val[l]!.2=rows.val[l]! ⦄ := by
  unfold split_ticket_loop
  apply range_fold (split_ticket_loop.body chunk base chunks rows) active journal
    (fun n out => ∀ l<n, out.val[l]!.1.val=base.val+l*chunks.val+chunk.val ∧ out.val[l]!.2=rows.val[l]!) (by simp)
  · intro it current stop live prior
    have lim := fit it.start.val live
    have laneFit : it.start.val*chunks.val≤Usize.max := by omega
    unfold split_ticket_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag,lift,bind_ok]
    step as ⟨off,ov⟩
    step as ⟨pre,pv⟩
    step as ⟨slot,sv⟩
    step as ⟨row,read⟩
    step as ⟨out,put⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    intro l hl
    rw [put,Array.set_val_eq]
    by_cases eq : l=it.start.val
    · subst l
      rw [setSame _ _ _ (by simp;omega)]
      exact ⟨by simp only [U32.cast_Usize_val_eq] at *;omega,by rw [read,←getElem!_pos]⟩
    · rw [setOther _ _ _ _ (Ne.symm eq)]
      exact prior l (by omega)
  · intro it rows last stop
    obtain ⟨n,no⟩ := ForsDriver.range_done it _ stop last
    simp [split_ticket_loop.body,no]
end slhdsa.ParallelForsTicket
