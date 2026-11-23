import Shakebatch.WotsHistogram
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.WotsOrder
open shake.batch
abbrev Mut := core.slice.iter.IterMut Usize

theorem bucket_starts (ds : List U32) (len : ds.length≤67)
    (original : Mut) (size : original.slice.length=16) (start : original.i=0)
    (counts : ∀ j < 16, original.slice.val[j]!.val=counted ds ds.length j) :
    chain_order_loop1 original (fun x => x) 0#usize ⦃ last finish =>
      (finish last).slice.length=16 ∧ ∀ j<16, (finish last).slice.val[j]!.val=below ds j ⦄ := by
  let invariant := fun (it : Mut) (back : Mut → Mut) =>
    ∀ future : Mut, future.slice.length=16 →
      (back future).slice.length=16 ∧ ∀ j<16,
        (back future).slice.val[j]!.val = if j < it.i then below ds j else future.slice.val[j]!.val
  unfold chain_order_loop1
  apply loop.spec_decr_nat (measure := fun q : Mut × (Mut → Mut) × Usize => 16-q.1.i)
    (inv := fun q => q.1.slice=original.slice ∧ q.1.i≤16 ∧ q.2.2.val=below ds q.1.i ∧ invariant q.1 q.2.1)
  · rintro ⟨it,back,atD⟩ ⟨s,within,total,holds⟩
    simp only at s within total holds
    unfold chain_order_loop1.body
    step with core.slice.iter.IteratorIterMut.next.spec it as ⟨o,it',nextBack,hSlice,none,some⟩
    cases o with
    | none =>
      obtain ⟨finished,hidx⟩ := some
      simp only [bind_ok,step_simps]
      obtain ⟨n,old⟩ := holds it' (by rw [hSlice,s,size])
      refine ⟨by simpa only [none] using n,?_⟩
      intro j hj
      simpa only [none,if_pos (show j < it.i by rw [s,size] at finished;omega)] using old j hj
    | some x =>
      obtain ⟨live,hx,nextIndex,replace⟩ := some
      have room : it.i<16 := by rwa [s,size] at live
      have count : x.val=counted ds ds.length it.i := by rw [hx,s,counts _ room]
      have offsetBound : below ds (it.i+1) ≤ ds.length := List.countP_le_length
      have fits : atD.val+x.val≤ds.length := by rw [total,count,← below_next];exact offsetBound
      step as ⟨newStart,add⟩
      refine ⟨hSlice.trans s,by omega,?_,?_,by omega⟩
      · rw [add,nextIndex,below_next,total,count]
      · intro future futureSize
        simp only []
        rw [replace]
        let newer : Mut := {future with slice:=future.slice.setAtNat it.i atD}
        have changed (j : Nat) : newer.slice.val[j]! = if j=it.i then atD else future.slice.val[j]! := by
          exact Slice.getElem!_Nat_setAtNat future.slice it.i j atD (by omega)
        obtain ⟨still,old⟩ := holds newer (by simp [newer,futureSize])
        refine ⟨still,?_⟩
        intro j hj
        change (back newer).slice.val[j]!.val=_
        rw [old j hj,changed]
        by_cases early : j < it.i
        · simp [early,nextIndex,show j < it.i+1 by omega]
        · by_cases same : j=it.i
          · subst j; simp [total,nextIndex]
          · simp [early,same,nextIndex,show ¬j < it.i+1 by omega]
  · refine ⟨rfl,show original.i≤16 by omega,?_,?_⟩
    · simp [start,below]
    · intro future good
      exact ⟨good,fun j _ => by simp [start]⟩

end slhdsa.ShakeBatch.WotsOrder
