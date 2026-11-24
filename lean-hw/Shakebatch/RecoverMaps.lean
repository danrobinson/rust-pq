import Shakebatch.RecoverProgram
import Shakebatch.Selection
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
open shake.fors_batch.recover

theorem recover_trees (N : Usize) (first active : Usize) (nonempty : 0 < active.val)
    (fit : first.val + active.val ≤ Usize.max) :
    core.array.from_fn machine.width (closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N)
      (first,active) ⦃ out => ∀ j < machine.width.val, out.val[j]!.val=treeAt first.val active.val j ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width
    (closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N) (first,active)
    (fun j (x : Usize) => x.val=treeAt first.val active.val j) ?_)
  · intro out h j hj; simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i _
  simp only [closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize,closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut]
  step as ⟨last,limit⟩
  simp only [lift,bind_ok]
  have cap : first.val + (core.cmp.impls.OrdUsize.min i last).val ≤ Usize.max := by
    simp only [core.cmp.impls.OrdUsize.min_val,limit]; omega
  step
  simp_all [treeAt,step_simps,core.cmp.impls.OrdUsize.min_val]
  rfl

theorem recover_indices {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (choices : Slice U32) (trees : Array Usize machine.width) (count : choices.length ≤ 35)
    (valid : ∀ j < machine.width.val, trees.val[j]!.val < choices.length)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    core.array.Array.map (closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) trees (p,choices)
      ⦃ out => ∀ j < machine.width.val, let t := trees.val[j]!.val
        out.val[j]!.val=t*2^p.a.val+choices.val[t]!.val ⦄ := by
  apply map_spec (closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) trees (p,choices)
    (fun j v => let t := trees.val[j]!.val; v.val=t*2^p.a.val+choices.val[t]!.val)
  intro j hj
  let t := trees.val[j]!
  have ht : t.val < choices.length := valid j hj
  have shift := fors_shl_arith p.a.val t.val hp.valid.a_le (by omega)
  have chosen := index t.val ht
  have height : p.a.val ≤ 14 := hp.valid.a_le
  have less : p.a.val < 32 := by omega
  have castVal : (UScalar.cast .U32 t).val=t.val := by
    simp [UScalar.cast_val_eq,Nat.mod_eq_of_lt (show t.val < 2^32 by omega)] <;> omega
  simp only [closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32,closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut,lift,bind_ok]
  step as ⟨shifted,sval⟩
  all_goals try exact less
  all_goals try scalar_tac
  have sv : shifted.val=t.val*2^p.a.val := by
    change shifted.val=((t.val)*2^p.a.val)
    rw [sval,show (UScalar.cast .U32 trees.val[j]!).val = t.val from castVal]
    simpa [U32.size,U32.numBits] using shift.1
  step as ⟨sel,read⟩
  have selectedVal : sel.val=choices.val[t.val]!.val := by rw [read,← getElem!_pos]
  step as ⟨v,add⟩
  simp only [step_simps,add,sv,selectedVal]
  exact ⟨rfl,rfl⟩

theorem recover_leaf_addresses (N : Usize) (a : address.Adrs) (indices : Array U32 machine.width) :
    core.array.Array.map (closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices a ⦃ out =>
      ∀ j < machine.width.val, out.val[j]! = {a with word2:=0#u32,word3:=indices.val[j]!} ⦄ := by
  apply map_spec (closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices a
    (fun j v => v = {a with word2:=0#u32,word3:=indices.val[j]!})
  intro j _
  simp [closure_3.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut,address.Adrs.with_word2,address.Adrs.with_word3,step_simps]

theorem recover_parents (N : Usize) (indices : Array U32 machine.width) :
    core.array.Array.map (closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < machine.width.val, out.val[j]!.val=indices.val[j]!.val / 2 ⦄ := by
  apply map_spec (closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices ()
    (fun j v => v.val=indices.val[j]!.val / 2)
  intro j _
  simp only [closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32,closure_7.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut]
  step
  simp [*,Nat.shiftRight_eq_div_pow]

theorem recover_parent_addresses (N : Usize) (a : address.Adrs) (level : U32) (bound : level.val < 32)
    (indices : Array U32 machine.width) :
    core.array.Array.map (closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,level) ⦃ out =>
      ∀ j < machine.width.val, adrsS out.val[j]! =
        {adrsS a with word2:=level.val+1,word3:=indices.val[j]!.val} ⦄ := by
  apply map_spec (closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,level)
    (fun j v => adrsS v = {adrsS a with word2:=level.val+1,word3:=indices.val[j]!.val})
  intro j _
  simp only [closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs,closure_8.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut]
  step
  simp [*,address.Adrs.with_word2,address.Adrs.with_word3,adrsS,step_simps]
  rfl
end slhdsa.ShakeBatch
