import Shakebatch.NodesProgram
import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

/-- Standard array map preserves all lane indices and the captured state of a stateless closure. -/
theorem map_spec {T F U : Type} [Inhabited T] [Inhabited U] {N : Usize}
    (inst : core.ops.function.FnMut F T U) (inputs : Array T N) (f : F) (post : Nat → U → Prop)
    (each : ∀ j < N.val, inst.call_mut f inputs.val[j]! ⦃ x g => post j x ∧ g=f ⦄) :
    core.array.Array.map inst inputs f ⦃ out => ∀ j < N.val, post j out.val[j]! ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! N _ f post ?_)
  · intro out h j hj; simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i bound
  change (do let x ← inputs.index_usize i; inst.call_mut f x) ⦃ _ _ => _ ⦄
  step as ⟨v,get⟩
  rw [get,← getElem!_pos]
  exact each i.val bound

end slhdsa.ShakeBatch
