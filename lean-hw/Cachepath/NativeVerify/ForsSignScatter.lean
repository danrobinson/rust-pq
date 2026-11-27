import Cachepath.NativeVerify.ForsSignScatterProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : ShakeBatch.Machine]
theorem addresses {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (prf : address.Adrs) (choices : Slice U32) (first active : Usize) (nonempty : 0 < active.val)
    (fit : first.val+active.val ≤ choices.length) (trees : choices.length ≤ 35)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    core.array.from_fn machine.width (sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N)
      (first,active,prf,p.a,choices) ⦃ out => ∀ j < machine.width.val,
        let tree := treeAt first.val active.val j
        out.val[j]! = {prf with word3 := out.val[j]!.word3} ∧ out.val[j]!.word3.val=tree*2^p.a.val+choices.val[tree]!.val ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width
    (sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N) (first,active,prf,p.a,choices)
    (fun j (x : address.Adrs) => let tree := treeAt first.val active.val j; x = {prf with word3 := x.word3} ∧ x.word3.val=tree*2^p.a.val+choices.val[tree]!.val) ?_)
  · intro out h j hj
    simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  have valid : treeAt first.val active.val i.val < choices.length := by unfold treeAt; omega
  have shift := fors_shl_arith p.a.val (treeAt first.val active.val i.val) hp.valid.a_le (by omega)
  have chosen := index _ valid
  simp only [sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs,sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut]
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
  simp_all only [address.Adrs.with_word3,step_simps]
  rfl


theorem store_secrets {N : Usize} (rows : Rows N) (first stride active : Usize)
    (sig : Buffer) (fit : (first.val+active.val)*stride.val ≤ sig.length)
    (width : active.val ≤ machine.width.val) (positive : 0 < N.val) (within : 0+N.val ≤ stride.val) :
    sign_loop0_loop0 ⟨0#usize,active⟩ stride sig first rows ⦃ out =>
      Scattered rows first.val stride.val 0 active.val sig out ⦄ :=
  ShakeBatch.write_secrets rows first stride active sig fit width positive within

theorem store_siblings {N : Usize} (rows : Rows N) (first stride active : Usize) (level : U32)
    (sig : Buffer) (fit : (first.val+active.val)*stride.val ≤ sig.length)
    (width : active.val ≤ machine.width.val) (positive : 0 < N.val) (within : ((level.val+1)*N.val)+N.val ≤ stride.val) :
    sign_loop1_loop0_loop0 ⟨0#usize,active⟩ stride sig first level rows ⦃ out =>
      Scattered rows first.val stride.val ((level.val+1)*N.val) active.val sig out ⦄ :=
  ShakeBatch.write_siblings rows first stride active level sig fit width positive within

end slhdsa.NativeVerify.ForsSign
