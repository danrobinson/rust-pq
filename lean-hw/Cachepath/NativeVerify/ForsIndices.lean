import Cachepath.NativeVerify.ForsProgram
import Shakebatch.RecoverMaps
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem indices_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32) (first active : Usize)
    (indices : Array U32 machine.width) (count : choices.length≤35) (fits : first.val+active.val≤choices.length)
    (width : active.val≤machine.width.val) (valid : ∀ j<choices.length, choices.val[j]!.val < 2^p.a.val) :
    recover_loop0_loop0 ⟨0#usize,active⟩ p.a choices first indices ⦃ out =>
      ∀ j<active.val, out.val[j]!.val = (first.val+j)*2^p.a.val+choices.val[first.val+j]!.val ⦄ := by
  unfold recover_loop0_loop0
  apply range_fold (recover_loop0_loop0.body p.a choices first) active indices (fun n s =>
    ∀ j < n, s.val[j]!.val = (first.val+j)*2^p.a.val+choices.val[first.val+j]!.val)
  · simp
  · intro it cur stop live prior
    unfold recover_loop0_loop0.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨tree,treeEq⟩
    have hit : tree.val < choices.length := by omega
    have shift := fors_shl_arith p.a.val tree.val hp.valid.a_le (by omega)
    have chosen := valid _ hit
    have cast : (UScalar.cast .U32 tree).val=tree.val :=
      UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change tree.val < 2^32;omega)
    have less : p.a.val ≤ 14 := hp.valid.a_le
    simp only [lift,bind_ok]
    step with U32.ShiftLeft_spec (UScalar.cast .U32 tree) p.a (by omega) as ⟨shifted,shiftEq,_⟩
    have sv : shifted.val=tree.val*2^p.a.val := by
      rw [shiftEq,cast]
      simpa [U32.size,U32.numBits] using shift.1
    step as ⟨choice,read⟩
    have xv : choice.val=choices.val[tree.val]!.val := by rw [read,← getElem!_pos]
    step as ⟨v,add⟩
    step as ⟨updated,put⟩
    refine ⟨next,updated,rfl,ends.trans stop,inc,?_⟩
    intro j small
    rw [put,Array.set_val_eq]
    by_cases same : j=it.start.val
    · subst j
      rw [setSame _ _ _ (by simp;omega),add,sv,xv,treeEq]
    · rw [setOther _ _ _ _ (Ne.symm same),prior j (by omega)]
  · intro it cur last stop
    unfold recover_loop0_loop0.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Fors
