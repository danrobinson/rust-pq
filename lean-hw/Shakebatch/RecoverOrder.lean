import Shakebatch.RecoverMaps
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
open shake.fors_batch.recover

theorem recover_left {N : Usize} (indices : Array U32 machine.width)
    (xs ys : Array (Array U8 N) machine.width) :
    core.array.from_fn machine.width (closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N)
      (indices,xs,ys) ⦃ out => ∀ j < machine.width.val,
        out.val[j]! = if indices.val[j]!.val % 2 = 0 then xs.val[j]! else ys.val[j]! ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width
    (closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) (indices,xs,ys)
    (fun j x => x = if indices.val[j]!.val % 2 = 0 then xs.val[j]! else ys.val[j]!) ?_)
  · intro out h j hj; simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  simp only [closure_5.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut]
  step as ⟨idx,get⟩
  have read : idx=indices.val[i.val]! := by rw [get,← getElem!_pos]
  simp only [lift,bind_ok]
  have bit : (idx &&& 1#u32).val = indices.val[i.val]!.val%2 := by
    rw [read]; simp [Nat.and_one_is_mod]
  by_cases hz : idx &&& 1#u32 = 0#u32
  · have zero : indices.val[i.val]!.val%2=0 := by rw [← bit,hz]; rfl
    simp only [hz,zero,if_true,↓reduceIte]
    step as ⟨x,hx⟩
    exact ⟨by rw [hx,← getElem!_pos],rfl⟩
  · have nz : indices.val[i.val]!.val%2≠0 := by intro h; apply hz; scalar_tac
    simp only [hz,nz,if_false,↓reduceIte]
    step as ⟨y,hy⟩
    exact ⟨by rw [hy,← getElem!_pos],rfl⟩

theorem recover_right {N : Usize} (indices : Array U32 machine.width)
    (xs ys : Array (Array U8 N) machine.width) :
    core.array.from_fn machine.width (closure_6.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N)
      (indices,xs,ys) ⦃ out => ∀ j < machine.width.val,
        out.val[j]! = if indices.val[j]!.val % 2 = 0 then xs.val[j]! else ys.val[j]! ⦄ := by
  exact recover_left indices xs ys

end slhdsa.ShakeBatch
