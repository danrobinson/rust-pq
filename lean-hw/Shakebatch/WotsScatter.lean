import Shakebatch.WotsOffsets
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.WotsOrder
open shake.batch

abbrev Enumerated := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32)

theorem scatter (digits : Slice U32) (offsets : Array Usize 16#usize) (order : Array Usize 67#usize)
    (starts : ∀ d < 16, offsets.val[d]!.val = below digits.val d)
    (len : digits.length≤67) (small : ∀ i < digits.length, digits.val[i]!.val<16) :
    chain_order_loop2 ⟨⟨digits,0⟩,0#usize⟩ offsets order ⦃ out =>
      ∀ i < digits.length, out.val[rank digits.val i]!.val=i ⦄ := by
  unfold chain_order_loop2
  apply loop.spec_decr_nat (measure := fun q : Enumerated × Array Usize 16#usize × Array Usize 67#usize => digits.length-q.1.iter.i)
    (inv := fun q => q.1.iter.slice=digits ∧ q.1.iter.i≤digits.length ∧ q.1.count.val=q.1.iter.i ∧
      (∀ d < 16, q.2.1.val[d]!.val=below digits.val d+counted digits.val q.1.iter.i d) ∧
      ∀ i < q.1.iter.i, q.2.2.val[rank digits.val i]!.val=i)
  · rintro ⟨⟨⟨ds,i⟩,ctr⟩,offs,ord⟩ ⟨rfl,within,clock,cursors,written⟩
    simp only at within clock cursors written
    unfold chain_order_loop2.body core.iter.adapters.enumerate.IteratorEnumerate.next
    simp only [core.iter.traits.iterator.IteratorSliceIter,core.slice.iter.IteratorSliceIter.next]
    by_cases live : i<ds.length
    · have hl : i < ds.len.val := by simpa using live
      simp only [dif_pos hl,bind_ok,lift]
      step as ⟨newCount,bump⟩
      let d := ds.val[i]!.val
      have digit : d<16 := small i live
      have ix : (UScalar.cast .Usize ds[i]).val=d := by
        rw [UScalar.cast_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
        change ds.val[i].val=ds.val[i]!.val
        rw [getElem!_pos ds.val i live]
        rfl
      step as ⟨slot,back,get,write⟩
      have atSlot : slot.val = rank ds.val i := by
        rw [get,← getElem!_pos,ix,cursors _ digit]
        rfl
      have slotValid : slot.val < 67 := by rw [atSlot];exact (rank_lt ds.val i live).trans_le len
      step as ⟨ord',upd⟩
      step as ⟨slot',incr⟩
      refine ⟨by omega,by omega,?_,?_,by omega⟩
      · intro j hj
        rw [write,Array.set_val_eq,ix,count_next _ _ _ live]
        by_cases same : d=j
        · subst j; rw [setSame _ _ _ (by simpa using digit),incr,atSlot,if_pos rfl]
          simp only [rank,d,Nat.add_assoc]
        · rw [setOther _ _ _ _ same,cursors _ hj,if_neg same,Nat.add_zero]
      · intro j hj
        rw [upd,Array.set_val_eq,atSlot]
        by_cases same : j=i
        · subst j;rw [setSame _ _ _ (by simpa [atSlot] using slotValid),clock]
        · have lt : j < i := by omega
          have jValid : j<ds.val.length := lt.trans live
          have diff : rank ds.val i≠rank ds.val j := fun eq => same (rank_injective ds.val jValid live eq.symm)
          rw [setOther _ _ _ _ diff,written _ lt]
    · have hl : ¬ i < ds.len.val := by simpa using live
      simp only [dif_neg hl,step_simps]
      intro j hj; exact written j (by omega)
  · refine ⟨rfl,Nat.zero_le _,rfl,?_,by simp⟩
    intro d hd;simpa [counted] using starts d hd

theorem order_spec (digits : Slice U32) (len : digits.length≤67)
    (small : ∀ i < digits.length, digits.val[i]!.val<16) :
    chain_order digits ⦃ out => ∀ i < digits.length, out.val[rank digits.val i]!.val=i ⦄ := by
  unfold chain_order
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  step with histogram digits len small as ⟨counts,totals⟩
  step with core.slice.MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter.spec counts as ⟨it,back,data,idx,restore⟩
  have size : it.slice.length=16 := by simp [Slice.length,data]
  step with bucket_starts digits.val len it size idx (by simpa only [data] using totals) as ⟨last,finish,sz,starts⟩
  simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
  apply scatter digits _ _ _ len small
  intro j hj
  rw [restore _ (by rw [sz]),starts _ hj]

theorem order_at {digits : List U32} (a : Array Usize 67#usize)
    (packed : ∀ i < digits.length, a.val[rank digits i]!.val=i)
    (j : Nat) (valid : j<digits.length) :
    a.val[j]!.val < digits.length ∧ rank digits a.val[j]!.val=j := by
  let f : Fin digits.length → Fin digits.length := fun x => ⟨rank digits x.val,rank_lt digits x.val x.isLt⟩
  have inj : Function.Injective f := by
    intro x y eq
    exact Fin.ext (rank_injective digits x.isLt y.isLt (congrArg Fin.val eq))
  obtain ⟨i,e⟩ := Finite.surjective_of_injective inj ⟨j,valid⟩
  have r : rank digits i.val=j := congrArg Fin.val e
  have value := packed i.val i.isLt
  rw [r] at value
  simpa only [value] using And.intro i.isLt r

#print axioms order_spec
end slhdsa.ShakeBatch.WotsOrder
