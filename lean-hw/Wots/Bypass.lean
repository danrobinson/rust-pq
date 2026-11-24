import Wots.Ordering
import Wots.Placement
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512

abbrev Buffers := Rows 64#usize
def element (N : Usize) (sig : Slice U8) (i : Nat) := (sig.val.drop (N.val*i)).take N.val

theorem direct_step (N : Usize) (sig : Slice U8) (out : Buffers) (it next : core.slice.iter.Iter Usize) (i : Usize)
    (advance : core.slice.iter.IteratorSliceIter.next it = ok (some i,next))
    (width : N.val ≤ 32) (key : i.val < out.length)
    (capacity : N.val*(i.val+1) ≤ sig.length) :
    recover_loop3.body N sig it out ⦃ flow => ∃ r, flow = cont (next,r) ∧
      piece out r i.val 22 (element N sig i.val) ⦄ := by
  unfold recover_loop3.body
  simp only [advance,bind_ok]
  have sigmax : sig.length ≤ Usize.max := sig.property
  have imax : i.val+1 ≤ Usize.max := by have := out.property; change out.length ≤ Usize.max at this; omega
  have bytes : N.val*(i.val+1) = N.val*i.val+N.val := Nat.mul_succ ..
  step as ⟨a,restore,ha,hback⟩
  step as ⟨stop,hs⟩
  step as ⟨dst,restoreBytes,hsub,hlen,hrestore⟩
  step as ⟨lo,hlo⟩
  step as ⟨j,hj⟩
  step as ⟨hi,hhi⟩
  have e : hi.val = lo.val+N.val := by rw [hhi,hj,hlo]; exact bytes
  step as ⟨src,hsrc,hsize⟩
  step as ⟨copied,hc⟩
  · change dst.length=src.length
    rw [hlen,hsize]; scalar_tac
  have enough : N.val ≤ sig.val.length-N.val*i.val := by change N.val ≤ sig.length-N.val*i.val; omega
  have srcOK : src.val = element N sig i.val := by
    rw [hsrc]; simp [element,List.slice,List.drop_take,e,hlo]
  have elen : (element N sig i.val).length = N.val := by simp [element,Nat.min_eq_left enough]
  refine ⟨_,rfl,?_,?_,?_⟩
  · rw [hback]; simp
  · intro r other
    rw [hback,Slice.set_val_eq,Avx2.setOther _ _ _ _ (Ne.symm other)]
  · rw [hback,Slice.set_val_eq,Avx2.setSame _ _ _ key,hrestore,hc,srcOK]
    have ok : (element N sig i.val).length ≤ out.val[i.val]!.val.length-22 := by simp [elen]; omega
    simp only [List.setSlice!,show (22#usize).val = 22 by rfl,Nat.min_eq_left ok,List.take_length,ha,← getElem!_pos]


/-- After processing a prefix of the bypass list, each visited row contains its
signature element at byte 22. Other rows and the surrounding bytes agree with the input. -/
def bypassed (N : Usize) (sig : Slice U8) (initial out : Buffers) (list : Slice Usize) (count : Nat) :=
  out.length = initial.length ∧ ∀ r < initial.length,
    if ∃ t < count, list.val[t]!.val = r then
      out.val[r]!.val = initial.val[r]!.val.take 22 ++ element N sig r ++ initial.val[r]!.val.drop (22+N.val)
    else out.val[r]! = initial.val[r]!

theorem bypass_spec (N : Usize) (sig : Slice U8) (initial : Buffers) (list : Slice Usize)
    (width : N.val ≤ 32) (capacity : ∀ t < list.length, N.val*(list.val[t]!.val+1) ≤ sig.length)
    (keys : ∀ t < list.length, list.val[t]!.val < initial.length)
    (distinct : ∀ i < list.length, ∀ j < list.length, list.val[i]!.val = list.val[j]!.val → i=j) :
    recover_loop3 N ⟨list,0⟩ sig initial ⦃ out => bypassed N sig initial out list list.length ⦄ := by
  unfold recover_loop3
  apply loop.spec_decr_nat (measure := fun p : core.slice.iter.Iter Usize × Buffers => list.length-p.1.i)
    (inv := fun p => p.1.slice = list ∧ p.1.i ≤ list.length ∧ bypassed N sig initial p.2 list p.1.i)
  · rintro ⟨⟨s,t⟩,buf⟩ ⟨rfl,ht,prev⟩
    simp only at ht prev distinct keys capacity
    by_cases live : t < s.length
    · let key := s.val[t]!
      let next : core.slice.iter.Iter Usize := ⟨s,t+1⟩
      have adv : core.slice.iter.IteratorSliceIter.next ⟨s,t⟩ = ok (some key,next) := by
        simp only [core.slice.iter.IteratorSliceIter.next,dif_pos (show t < s.len.val by simpa using live)]
        dsimp [key,next]; rw [getElem!_pos s.val t live]; rfl
      have bound : key.val < initial.length := keys t live
      have cap : N.val*(key.val+1) ≤ sig.length := capacity t live
      have stored := direct_step N sig buf ⟨s,t⟩ next key adv width (prev.1 ▸ bound) cap
      apply WP.spec_mono stored
      rintro flow ⟨out,rfl,update⟩
      refine ⟨⟨rfl,by change t+1 ≤ s.length; omega,update.1.trans prev.1,?_⟩,by change s.length-(t+1)<s.length-t; omega⟩
      intro r hr
      by_cases target : key.val=r
      · subst r
        have fresh : ¬∃ i<t, s.val[i]!.val=key.val := by
          rintro ⟨i,hi,eq⟩; have := distinct i (by omega) t live eq; omega
        have now : ∃ i<t+1, s.val[i]!.val=key.val := ⟨t,by omega,rfl⟩
        have same := prev.2 key.val hr
        rw [if_neg fresh] at same
        have elen : (element N sig key.val).length = N.val := by
          have enough : N.val ≤ sig.val.length-N.val*key.val := by
            change N.val ≤ sig.length-N.val*key.val
            rw [Nat.mul_succ] at cap; omega
          simp [element,Nat.min_eq_left enough]
        simpa only [next,if_pos now,elen,same] using update.2.2
      · have same := update.2.1 r (Ne.symm target)
        have visited : (∃ i<t+1, s.val[i]!.val=r) ↔ (∃ i<t, s.val[i]!.val=r) := by
          constructor
          · rintro ⟨i,hi,eq⟩
            have ne : i ≠ t := by rintro rfl; exact target eq
            exact ⟨i,by omega,eq⟩
          · rintro ⟨i,hi,eq⟩; exact ⟨i,by omega,eq⟩
        simpa only [next,visited,same] using prev.2 r hr
    · unfold recover_loop3.body
      simp only [core.slice.iter.IteratorSliceIter.next,dif_neg (show ¬t<s.len.val by simpa using live),bind_ok,step_simps]
      exact (show t=s.length by omega) ▸ prev
  · simp [bypassed]

end slhdsa.X86.Wots
