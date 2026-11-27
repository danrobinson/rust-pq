import Cachepath.NativeVerify.WotsLoad
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def InitialLanes (N n : Usize) (sig : Slice U8) (digits : Slice U32) (order : Array Usize 67#usize)
    (count : Nat) (ids : Array Usize machine.width) (steps : Array U32 machine.width)
    (values : LaneValues machine.width) : Prop := ∀ l < count,
  let id := order.val[l]!
  ids.val[l]! = id ∧ steps.val[l]! = digits.val[id.val]! ∧
    ∀ k < n.val, laneWord values l k = inputWord ((sig.val.drop (id.val*N.val)).take N.val) k

theorem initialize_lanes (N n active : Usize) (sig : Slice U8) (digits : Slice U32) (order : Array Usize 67#usize)
    (ids : Array Usize machine.width) (steps : Array U32 machine.width) (values : LaneValues machine.width)
    (room : active.val ≤ machine.width.val) (cap : active.val ≤ 67)
    (indices : ∀ l < active.val, order.val[l]!.val < digits.length)
    (fits : digits.length*N.val ≤ sig.length) (bounded : digits.length≤67)
    (words : n.val*8 = N.val) (ncap : n.val≤4) :
    recover_loop1 N ⟨0#usize,active⟩ sig digits n order 0#usize ids steps values ⦃ out =>
      out.1.val = active.val ∧ InitialLanes N n sig digits order active.val out.2.1 out.2.2.1 out.2.2.2 ⦄ := by
  unfold recover_loop1
  apply range_fold (fun it (v : Usize × Array Usize machine.width × Array U32 machine.width × LaneValues machine.width) =>
    recover_loop1.body N sig digits n order it v.1 v.2.1 v.2.2.1 v.2.2.2) active (0#usize,ids,steps,values)
    (fun i v => v.1.val=i ∧ InitialLanes N n sig digits order i v.2.1 v.2.2.1 v.2.2.2)
  · simp [InitialLanes]
  · rintro it ⟨pos,ids,steps,values⟩ stop live ⟨cursor,prior⟩
    change pos.val=it.start.val at cursor
    unfold recover_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨id,atId⟩
    rw [← getElem!_pos] at atId
    have good : id.val < digits.length := by simpa [atId,cursor] using indices _ live
    have size := (Nat.mul_le_mul_right N.val good).trans fits
    step as ⟨pos',inc⟩
    step as ⟨ids',setId⟩
    step as ⟨digit,atDigit⟩
    rw [← getElem!_pos] at atDigit
    step as ⟨steps',setStep⟩
    step as ⟨start,first⟩
    step as ⟨succ,up⟩
    step as ⟨limit,last⟩
    step as ⟨blk,view,len⟩
    have delta : limit.val = start.val+N.val := by rw [last,up,first,Nat.add_mul]; simp
    step with load_lane values it.start n blk (by omega) ncap (by omega) as ⟨vv,stored⟩
    refine ⟨next,(pos',ids',steps',vv),rfl,ends.trans stop,idx,by simpa using (show pos'.val=next.start.val by omega),?_⟩
    intro l hl
    rw [setId,setStep,Array.set_val_eq,Array.set_val_eq]
    by_cases eq : l=it.start.val
    · subst l
      rw [setSame _ _ _ (by simpa using live.trans_le room),setSame _ _ _ (by simpa using live.trans_le room)]
      have atId' : id=order.val[it.start.val]! := by simpa [cursor] using atId
      refine ⟨atId',by rw [← atId']; exact atDigit,?_⟩
      intro k hk
      rw [stored,ite_eq_left ⟨rfl,hk⟩,← atId']
      simp [view,List.slice,first,delta]
    · have lt : l < it.start.val := by omega
      obtain ⟨oldId,oldStep,oldVal⟩ := prior l lt
      rw [setOther _ _ _ _ (Ne.symm eq),setOther _ _ _ _ (Ne.symm eq)]
      refine ⟨oldId,oldStep,?_⟩
      intro k hk
      simpa [stored,eq] using oldVal k hk
  · rintro it ⟨pos,ids,steps,values⟩ last stop
    unfold recover_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Wots
