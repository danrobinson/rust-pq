import Shakebatch.SignProgram
import Shakebatch.ForsNodes
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
open shake.fors_batch.sign

def treeAt (first active j : Nat) := first + min j (active-1)

theorem selected {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (choices : Slice U32) (first active : Usize) (nonempty : 0 < active.val)
    (fit : first.val+active.val ≤ choices.length) (trees : choices.length ≤ 35)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    core.array.from_fn machine.width (closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (first,active,p,choices) ⦃ out => ∀ j < machine.width.val,
        let tree := treeAt first.val active.val j
        out.val[j]!.val=tree*2^p.a.val+choices.val[tree]!.val ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width
    (closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) (first,active,p,choices)
    (fun j (x : U32) => let tree := treeAt first.val active.val j; x.val=tree*2^p.a.val+choices.val[tree]!.val) ?_)
  · intro out h j hj
    simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  have valid : treeAt first.val active.val i.val < choices.length := by unfold treeAt; omega
  have shift := fors_shl_arith p.a.val (treeAt first.val active.val i.val) hp.valid.a_le (by omega)
  have chosen := index _ valid
  simp only [closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32,closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut]
  step as ⟨last,limit⟩
  have cap : first.val + (core.cmp.impls.OrdUsize.min i last).val ≤ Usize.max := by
    simp only [core.cmp.impls.OrdUsize.min_val,limit]
    unfold treeAt at valid; scalar_tac
  simp only [lift,bind_ok]
  step as ⟨tree,ix⟩
  have tv : tree.val=treeAt first.val active.val i.val := by
    simp [ix,treeAt,limit,core.cmp.impls.OrdUsize.min_val]
  have treeBound : tree.val < choices.length := by rw [tv]; exact valid
  have height : p.a.val ≤ 14 := hp.valid.a_le
  have castVal : (UScalar.cast .U32 tree).val=tree.val := by
    simp [UScalar.cast_val_eq,Nat.mod_eq_of_lt (show tree.val < 2^32 by omega)] <;> omega
  step as ⟨shifted,sval⟩
  all_goals try scalar_tac
  have sv : shifted.val=tree.val*2^p.a.val := by
    rw [sval,castVal,tv]
    simpa [U32.size,U32.numBits] using shift.1
  step as ⟨sel,read⟩
  have selectedVal : sel.val=choices.val[tree.val]!.val := by rw [read,← getElem!_pos]
  step
  simp_all only [step_simps]
  rfl

theorem sibling_indices (N : Usize) (indices : Array U32 machine.width) (j : U32) (fit : j.val < 32) :
    core.array.Array.map (closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices j ⦃ out =>
      ∀ i < machine.width.val, out.val[i]!.val=(indices.val[i]!.val / 2^j.val) ^^^ 1 ⦄ := by
  apply map_spec (closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices j
    (fun i out => out.val = (indices.val[i]!.val / 2^j.val) ^^^ 1)
  intro i _
  simp only [closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32,closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut]
  step as ⟨v,shift,bit⟩
  simp only [lift,bind_ok,step_simps,UScalar.val_xor,shift,Nat.shiftRight_eq_div_pow]
  rfl
end slhdsa.ShakeBatch
