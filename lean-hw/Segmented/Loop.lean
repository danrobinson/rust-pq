import Segmented.Funs
import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result
namespace slhdsa.Segmented

/-- A complete block of input advances the state. Finishing with its suffix
must give the same digest as finishing before consuming the block. -/
structure Hash (T R D : Type) where
  digest : T → Nat → List U8 → D
  output : R → D

abbrev Impl := SegmentedRust.slh.message.MessageHash

def BlockRule {T R D H B} (model : Hash T R D) (alg : Impl H T R B) :=
  ∀ st (data : Slice U8) (off : Usize), off.val+B.val≤data.length →
    alg.compress st data off ⦃ next => ∀ prior suffix,
      model.digest next (prior+B.val) suffix =
        model.digest st prior (((data.val.drop off.val).take B.val) ++ suffix) ⦄

theorem prefix_loop {T R D H} (model : Hash T R D) (B : Usize) (width : 0<B.val)
    (alg : Impl H T R B) (stepBlock : BlockRule model alg)
    (initial : T) (pre : Nat) (front msg : Slice U8) :
    SegmentedRust.slh.message.continued_loop alg initial front 0#usize ⦃ st pos =>
      pos.val≤front.length ∧ front.length-pos.val<B.val ∧ pos.val%B.val=0 ∧
      model.digest st (pre+pos.val) (front.val.drop pos.val ++ msg.val) =
        model.digest initial pre (front.val ++ msg.val) ⦄ := by
  unfold SegmentedRust.slh.message.continued_loop
  apply loop.spec_decr_nat (measure := fun q : T × Usize => front.length-q.2.val)
    (inv := fun q => q.2.val≤front.length ∧ q.2.val%B.val=0 ∧
      model.digest q.1 (pre+q.2.val) (front.val.drop q.2.val ++ msg.val) =
        model.digest initial pre (front.val ++ msg.val))
  · rintro ⟨st,pos⟩ ⟨bound,aligned,digest⟩
    simp only at bound aligned digest ⊢
    unfold SegmentedRust.slh.message.continued_loop.body
    step as ⟨left,leftVal⟩
    split
    · rename_i enough
      have room : pos.val+B.val≤front.length := by scalar_tac
      step with stepBlock st front pos room as ⟨next,consume⟩
      step as ⟨endPos,endVal⟩
      refine ⟨by omega,by rw [endVal,Nat.add_mod,aligned]; simp,?_,by omega⟩
      rw [endVal,←Nat.add_assoc,consume,←List.append_assoc,←digest]
      rw [show front.val.drop (pos.val+B.val)=(front.val.drop pos.val).drop B.val by simp]
      rw [List.take_append_drop]
    · simp only [step_simps]
      refine ⟨bound,?_,aligned,digest⟩
      scalar_tac
  · simp
end slhdsa.Segmented
