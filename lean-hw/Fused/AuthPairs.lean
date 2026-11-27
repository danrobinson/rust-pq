import Fused.Program
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused
open ShakeBatch

def PairRows {N : Usize} (prs : Slice Usize) (base : U32) (nodes : Array (Array U8 N) 8#usize) (a : address.Adrs)
    (count : Nat) (addrs : Array address.Adrs 8#usize) (left right : Array (Array U8 N) 8#usize) :=
  ∀ j < count, (adrsS addrs.val[j]!)={adrsS a with word2:=1,word3:=base.val/2+prs.val[j]!.val} ∧
    left.val[j]! =nodes.val[2*prs.val[j]!.val]! ∧ right.val[j]! =nodes.val[2*prs.val[j]!.val+1]!

theorem prepare_pairs {N : Usize} (prs : Slice Usize) (base : U32) (nodes : Array (Array U8 N) 8#usize)
    (tree : address.Adrs) (addrs : Array address.Adrs 8#usize) (left right : Array (Array U8 N) 8#usize)
    (width : prs.length≤8) (bounds : ∀ j < prs.length, prs.val[j]!.val<4) :
    xmss_sign_batch_loop4 ⟨⟨prs,0⟩,0#usize⟩ base nodes tree addrs left right ⦃ out left' right' =>
      PairRows prs base nodes tree prs.length out left' right' ⦄ := by
  unfold xmss_sign_batch_loop4
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Usize) ×
      Array address.Adrs 8#usize × Array (Array U8 N) 8#usize × Array (Array U8 N) 8#usize => prs.length-q.1.iter.i)
    (inv := fun q => q.1.iter.slice=prs ∧ q.1.iter.i≤prs.length ∧ q.1.count.val=q.1.iter.i ∧
      PairRows prs base nodes tree q.1.iter.i q.2.1 q.2.2.1 q.2.2.2)
  · rintro ⟨it,addresses,ls,rs⟩ ⟨slice,limit,count,prior⟩
    simp only at slice limit count prior ⊢
    unfold xmss_sign_batch_loop4.body
    have plen : prs.val.length=prs.length := rfl
    by_cases more : it.iter.i<prs.length
    · let next : core.slice.iter.Iter Usize := { it.iter with i:=it.iter.i+1 }
      have inner : core.slice.iter.IteratorSliceIter.next it.iter = ok (some prs.val[it.iter.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,next,slice,more]
      dsimp only [core.iter.adapters.enumerate.IteratorEnumerate.next,core.iter.traits.iterator.IteratorSliceIter]
      rw [inner]
      simp only [bind_ok,bind_assoc]
      step as ⟨cnt,inc⟩
      step as ⟨a,level⟩
      step as ⟨shift,sv,_⟩
      simp only [lift,bind_ok]
      have validIndex : it.iter.i<prs.val.length := more
      have pr : prs.val[it.iter.i].val<4 := by simpa [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem validIndex] using bounds _ more
      have cast : (UScalar.cast .U32 prs.val[it.iter.i]).val=prs.val[it.iter.i].val := by scalar_tac
      have baseMax : base.val<2^32 := base.hmax
      have low : shift.val=base.val/2 := by simpa [Nat.shiftRight_eq_div_pow] using sv
      step as ⟨word,wordVal⟩
      step as ⟨a',index⟩
      step as ⟨addresses',wa⟩
      step as ⟨li,lv⟩
      step as ⟨ln,ld⟩
      step as ⟨ls',wl⟩
      step as ⟨ri,rv⟩
      step as ⟨rn,rd⟩
      step as ⟨rs',wr⟩
      refine ⟨slice,by dsimp [next];omega,by dsimp [next];omega,?_,by dsimp [next];omega⟩
      intro j live
      change j < it.iter.i+1 at live
      rw [wa,wl,wr,Array.set_val_eq,Array.set_val_eq,Array.set_val_eq]
      by_cases same : j=it.count.val
      · subst j
        rw [setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega)]
        rw [index,level,ld,rd,← getElem!_pos,← getElem!_pos]
        simp [adrsS,wordVal,low,cast,rv,lv,count,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem validIndex]
      · rw [setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same)]
        exact prior j (by omega)
    · have inner : core.slice.iter.IteratorSliceIter.next it.iter = ok (none,it.iter) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length] at *
      simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,core.iter.traits.iterator.IteratorSliceIter,
        inner,bind_ok,step_simps]
      exact (show it.iter.i=prs.length by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,rfl,by intro j h;change j<0 at h;omega⟩

end slhdsa.Fused
