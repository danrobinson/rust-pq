import Shakebatch.WotsSignProgram
import Shakebatch.WotsScatter
import Shakebatch.Map
import Slhdsa.Proofs.Util
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem batch_ids {N : Usize} (batch : Slice Usize) (nonempty : 0 < batch.length) :
    core.array.from_fn machine.width (shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N) batch
      ⦃ out => ∀ j < machine.width.val, out.val[j]! = batch.val[min j (batch.length-1)]! ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width _ batch
    (fun j v => v=batch.val[min j (batch.length-1)]!) ?_)
  · intro out lane j hj;simpa only [Array.getElem!_Nat_eq] using lane j hj
  intro i hi
  change shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut (N:=N) batch i ⦃ _ ⦄
  unfold shake.batch.sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  step as ⟨last,idx⟩
  rw [Slice.len_val] at idx
  simp only [lift,bind_ok]
  have pos : (core.cmp.impls.OrdUsize.min i last).val=min i.val (batch.length-1) := by
    change (if last.val < i.val then last else i).val=_
    split <;> rename_i h
    · rw [min_eq_right (by omega),idx]
    · rw [min_eq_left (by omega)]
  step as ⟨v,found⟩
  rw [found,← getElem!_pos,pos]

theorem limit_digits {N : Usize} (digits : Slice U32) (ids : Array Usize machine.width)
    (bound : ∀ j < machine.width.val, ids.val[j]!.val < digits.length) :
    core.array.Array.map (shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) ids digits
      ⦃ out => ∀ j < machine.width.val, out.val[j]! = digits.val[ids.val[j]!.val]! ⦄ := by
  apply map_spec (shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) ids digits
    (fun j (r : U32) => r=digits.val[ids.val[j]!.val]!)
  intro j hj
  change shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut (N:=N) digits ids.val[j]! ⦃ _ ⦄
  unfold shake.batch.sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  step as ⟨d,found⟩
  rw [found,← getElem!_pos]

theorem recover_blocks {N : Usize} (sig : Slice U8) (ids : Array Usize machine.width)
    (bound : ∀ j < machine.width.val, (ids.val[j]!.val+1)*N.val ≤ sig.length) :
    core.array.Array.map (shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids sig
      ⦃ out => ∀ j < machine.width.val, out.val[j]!.val=(sig.val.drop (ids.val[j]!.val*N.val)).take N.val ⦄ := by
  apply map_spec (shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids sig
    (fun j (r : Array U8 N) => r.val=(sig.val.drop (ids.val[j]!.val*N.val)).take N.val)
  intro j hj
  change shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut (N:=N) sig ids.val[j]! ⦃ _ ⦄
  unfold shake.batch.recover.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  step with block_spec N sig ids.val[j]! (bound j hj) as ⟨block,found⟩
  exact found

end slhdsa.ShakeBatch
