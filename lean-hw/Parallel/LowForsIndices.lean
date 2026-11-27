import Parallel.LowForsProgram
import Parallel.ForsTicketIndices
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLowFors
open ShakeBatch
variable [machine : Machine]
set_option allowUnsafeReducibility true in
attribute [local reducible] ticket.closure ticket.closure_1

def absolute (choices : alloc.vec.Vec U32) (a : U32) (t : Nat) :=
  t*2^a.val+choices.val[t]!.val

theorem absolute_indices (N first active : Usize) (a : U32) (choices : alloc.vec.Vec U32)
    (ha : a.val≤14) (count : choices.length≤35) (enabled : 0<active.val)
    (capacity : first.val+active.val≤choices.length) (digits : ∀ i<choices.length, choices.val[i]!.val<2^a.val) :
    core.array.from_fn machine.width (ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (first,active,a,choices) ⦃ out => ∀ l<machine.width.val,
      out[l]!.val=absolute choices a (ParallelForsTicket.treeAt first.val active.val l) ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! machine.width _ _ (fun l (v : U32) => v.val=absolute choices a (ParallelForsTicket.treeAt first.val active.val l))
  intro lane _
  change ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut (N:=N) (first,active,a,choices) lane ⦃ _ ⦄
  unfold ticket.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  step as ⟨last,lv⟩
  let off := core.cmp.impls.OrdUsize.min lane last
  have offv : off.val=min lane.val (active.val-1) := by
    change (if last<lane then last else lane).val=_
    rw [←lv]
    split <;> rename_i e
    · exact (min_eq_right (Nat.le_of_lt e)).symm
    · exact (min_eq_left (Nat.le_of_not_gt e)).symm
  simp only [lift,bind_ok]
  step as ⟨idx,iv⟩
  change idx.val=first.val+off.val at iv
  have same : idx.val=ParallelForsTicket.treeAt first.val active.val lane.val := by rw [iv,offv];rfl
  have live : idx.val<choices.length := by rw [iv,offv];have := Nat.min_le_right lane.val (active.val-1);omega
  have cast : (UScalar.cast .U32 idx).val=idx.val := cast_u32_usize_val _ (by omega)
  obtain ⟨sh,bound⟩ := fors_shl_arith a.val idx.val ha (by omega)
  step with U32.ShiftLeft_spec (UScalar.cast .U32 idx) a (by omega) as ⟨shifted,eq,_⟩
  have sv : shifted.val=idx.val*2^a.val := by rw [eq,cast];simpa [U32.size,U32.numBits] using sh
  step as ⟨d,read⟩
  have dv : d.val=choices.val[idx.val]!.val := by rw [read,←getElem!_pos]
  have digit := digits idx.val live
  step as ⟨x,res⟩
  unfold absolute;rw [←same,res,sv,dv]


theorem sibling_indices (N : Usize) (indices : Array U32 machine.width) (j : U32) (small : j.val<32) :
    core.array.Array.map (ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices j ⦃ out =>
      ∀ l<machine.width.val, out.val[l]!.val=(indices.val[l]!.val/2^j.val)^^^1 ⦄ := by
  apply map_spec _ _ _ (fun l (v : U32) => v.val=(indices.val[l]!.val/2^j.val)^^^1)
  intro k hk
  change ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut (N:=N) j _ ⦃ _ ⦄
  unfold ticket.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
  step as ⟨v,div,_⟩
  simp [step_simps,lift,UScalar.val_xor,div,Nat.shiftRight_eq_div_pow]
end slhdsa.ParallelLowFors
