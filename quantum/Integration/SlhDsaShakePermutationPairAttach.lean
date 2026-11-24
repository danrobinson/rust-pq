import Integration.SlhDsaShakePermutationPairs

namespace Reduction.ShakePermutation.Pairs
open Classical Tails

def resultingRate (π : Permutation) (p : Rate × Capacity) (y : Capacity) : Rate :=
  rateOf (π (join p.1 (xorCap y p.2)))

/-- New intermediate rates which collide with each other after the same salt is applied. -/
noncomputable def together (π : Permutation) (pending : Finset (Rate × Capacity)) : Finset Capacity := by
  classical exact pending.biUnion fun p => pending.biUnion fun q =>
    if p = q then ∅ else Finset.univ.filter fun y => resultingRate π p y = resultingRate π q y

theorem mem_together (π : Permutation) (pending : Finset (Rate × Capacity)) (y : Capacity) :
    y ∈ together π pending ↔ ∃ p ∈ pending, ∃ q ∈ pending, p ≠ q ∧ resultingRate π p y = resultingRate π q y := by
  classical
  unfold together
  simp only [Finset.mem_biUnion]
  apply exists_congr; intro p
  apply and_congr_right; intro _
  apply exists_congr; intro q
  apply and_congr_right; intro _
  by_cases h : p = q <;> simp [h]

private theorem move (a b c : Capacity) : xorCap (xorCap a b) (xorCap b c) = xorCap a c := by
  funext i
  simp only [xorCap,UInt64.xor_assoc,← UInt64.xor_assoc (a := b i),UInt64.xor_self,UInt64.zero_xor]

private theorem inject_count {C : Type} [Fintype C] (P Q : C → Prop) [DecidablePred P] [DecidablePred Q]
    (f : C → C) (hf : Function.Injective f) (hp : ∀ c, P c → Q (f c)) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card :=
  Finset.card_le_card_of_injOn f (fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp c (Finset.mem_filter.mp hc).2⟩)
    (fun _ _ _ _ e => hf e)

private theorem small (π : Permutation) (he : ¬exceptional π) (p q : Rate × Capacity) (hp : p ≠ q) :
    (Finset.univ.filter fun y => resultingRate π p y = resultingRate π q y).card ≤ 31 := by
  classical
  have hr : p.1 ≠ q.1 ∨ xorCap p.2 q.2 ≠ (fun _ => 0) := by
    by_contra! hn
    apply hp
    exact Prod.ext hn.1 (funext fun i => UInt64.xor_eq_zero_iff.mp (congrFun hn.2 i))
  have bound : (salts π p.1 q.1 (xorCap p.2 q.2)).card ≤ 31 := by
    by_contra! h
    exact he ⟨p.1,q.1,_,hr,by omega⟩
  refine le_trans ?_ bound
  unfold salts
  apply inject_count _ _ (fun y => xorCap y p.2)
  · intro y z h
    funext i
    have e := congrArg (fun v => v ^^^ p.2 i) (congrFun h i)
    simpa only [xorCap,UInt64.xor_assoc,UInt64.xor_self,UInt64.xor_zero] using e
  · intro y hy
    unfold collision
    rw [move]
    exact hy

theorem together_card (π : Permutation) (he : ¬exceptional π) (pending : Finset (Rate × Capacity)) :
    (together π pending).card ≤ pending.card * pending.card * 31 := by
  classical
  let fiber := fun p q : Rate × Capacity => if p = q then (∅ : Finset Capacity) else
    Finset.univ.filter fun y => resultingRate π p y = resultingRate π q y
  have hb (p q) : (fiber p q).card ≤ 31 := by
    by_cases h : p = q
    · simp [fiber,h]
    · simpa only [fiber,ite_eq_right h] using small π he p q h
  calc
    _ ≤ ∑ p ∈ pending, ∑ q ∈ pending, (fiber p q).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ _p ∈ pending, ∑ _q ∈ pending, 31 := Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hb p q
    _ = _ := by simp [Nat.mul_assoc]

end Reduction.ShakePermutation.Pairs
#print axioms Reduction.ShakePermutation.Pairs.together_card
