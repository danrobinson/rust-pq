import Shakebatch.WotsRank
import Shakebatch.Seed
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.WotsOrder
open shake.batch

theorem histogram (digits : Slice U32) (len : digits.length≤67)
    (small : ∀ i < digits.length, digits.val[i]!.val<16) :
    chain_order_loop0 ⟨digits,0⟩ (Array.repeat 16#usize 0#usize) ⦃ out =>
      ∀ d < 16, out.val[d]!.val=counted digits.val digits.length d ⦄ := by
  unfold chain_order_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.slice.iter.Iter U32 × Array Usize 16#usize => digits.length-q.1.i)
    (inv := fun q => q.1.slice=digits ∧ q.1.i≤digits.length ∧
      ∀ d < 16, q.2.val[d]!.val=counted digits.val q.1.i d)
  · rintro ⟨⟨ds,i⟩,a⟩ ⟨rfl,le,pre⟩
    simp only at le pre
    unfold chain_order_loop0.body core.slice.iter.IteratorSliceIter.next
    by_cases live : i<ds.length
    · have sz : i<ds.val.length := live
      have hl : i < ds.len.val := by simpa using live
      simp only [dif_pos hl,bind_ok,lift]
      have digit := small i live
      have index : (UScalar.cast .Usize ds[i]).val=ds.val[i]!.val := by
        rw [UScalar.cast_val_eq,getElem!_pos ds.val i sz,Nat.mod_eq_of_lt (by scalar_tac)]
        rfl
      step as ⟨old,get⟩
      have atOld : old.val=counted ds.val i ds.val[i]!.val := by
        rw [get,← getElem!_pos,index,pre _ digit]
      have maxCount : counted ds.val i ds.val[i]!.val ≤ ds.length := by
        have lim : counted ds.val i ds.val[i]!.val ≤ (ds.val.take i).length := List.countP_le_length
        simp [Slice.length] at lim ⊢;omega
      step as ⟨newVal,incr⟩
      step as ⟨a',set⟩
      refine ⟨by omega,?_,by omega⟩
      intro d hd
      rw [count_next _ _ _ sz,set,Array.set_val_eq,index]
      by_cases same : ds.val[i]!.val=d
      · subst d
        rw [setSame _ _ _ (by simpa using digit),incr,atOld,if_pos rfl]
      · rw [setOther _ _ _ _ same,pre _ hd,if_neg same,Nat.add_zero]
    · have hl : ¬ i < ds.len.val := by simpa using live
      simp only [dif_neg hl,step_simps]
      intro d hd
      simpa only [show i=ds.length by omega] using pre d hd
  · refine ⟨rfl,Nat.zero_le _,?_⟩
    intro d hd
    change ((Array.repeat 16#usize 0#usize).val[d]!).val=0
    rw [Array.repeat_val,List.getElem!_replicate 0#usize (show d<(16#usize).val from hd)]
    rfl

end slhdsa.ShakeBatch.WotsOrder
