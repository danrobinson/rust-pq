import Buffered.ForsHorizontal.Rows
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsHorizontal
open ShakeBatch NativeVerify
abbrev Domain (a : address.Adrs) := a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32

theorem indices_spec (N : Usize) (base : U32) (room : base.val+8≤2^32) :
    core.array.from_fn 8#usize (subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) base
      ⦃ ids => ∀ j<8, ids.val[j]!.val=base.val+j ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize _ base
    (fun j (x : U32) => x.val=base.val+j) ?_)
  · intro out h j hj;simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  simp only [subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32,
    subtree.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut,lift,bind_ok]
  have small : i.val<8 := hi
  have cast : (UScalar.cast .U32 i).val=i.val := by scalar_tac
  step as ⟨x,v⟩ <;> try scalar_tac

end slhdsa.ForsHorizontal
