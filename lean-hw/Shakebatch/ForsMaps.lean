import Shakebatch.ForsSecrets
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
open shake.fors_batch.nodes

theorem node_addresses (N : Usize) (a : address.Adrs) (lvl : U32) (indices : Array U32 machine.width) :
    core.array.Array.map (closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,lvl) ⦃ out =>
      ∀ j < machine.width.val, out.val[j]! = {a with word2:=lvl,word3:=indices.val[j]!} ⦄ := by
  apply map_spec (closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,lvl) (fun j v => v = {a with word2:=lvl,word3:=indices.val[j]!})
  intro j _
  simp [closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs,closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut,
    address.Adrs.with_word2,address.Adrs.with_word3,step_simps]
  rfl

theorem left_indices (N : Usize) (indices : Array U32 machine.width)
    (fit : ∀ j < machine.width.val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < machine.width.val, out.val[j]!.val=2*indices.val[j]!.val ⦄ := by
  apply map_spec (closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () (fun j v => v.val=2*indices.val[j]!.val)
  intro j hj
  simp only [closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32,closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut]
  have valid := fit j hj
  step
  simp [*,Nat.mul_comm]

theorem right_indices (N : Usize) (indices : Array U32 machine.width)
    (fit : ∀ j < machine.width.val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < machine.width.val, out.val[j]!.val=2*indices.val[j]!.val+1 ⦄ := by
  apply map_spec (closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () (fun j v => v.val=2*indices.val[j]!.val+1)
  intro j hj
  simp only [closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32,closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut]
  have valid := fit j hj
  step
  step
  simp [*,Nat.mul_comm]

end slhdsa.ShakeBatch
