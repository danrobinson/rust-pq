import Cachepath.WotsOrderProgram
import Slhdsa.Proofs.Basic
import Mathlib.Data.Fintype.EquivFin

open Aeneas Aeneas.Std Result
namespace CacheopsRust.WotsOrder
open cache.shake_ops.simd

/-- Stable counting-sort position for chain i, including digits equal to zero. -/
def below (xs : List U32) (d : Nat) := xs.countP fun x => decide (x.val < d)
def count (xs : List U32) (i d : Nat) := (xs.take i).countP fun x => decide (x.val = d)
def rank (xs : List U32) (i : Nat) := below xs xs[i]!.val + count xs i xs[i]!.val

private theorem below_succ (xs : List U32) (d : Nat) :
    below xs (d+1) = below xs d + count xs xs.length d := by
  simp only [below,count,List.take_length]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons,decide_eq_true_eq]
    split_ifs <;> omega

private theorem nextCount (xs : List U32) (i d : Nat) (hi : i < xs.length) :
    count xs (i+1) d = count xs i d + if xs[i]!.val = d then 1 else 0 := by
  rw [count,List.take_succ_eq_append_getElem hi,List.countP_append]
  simp [count,hi]

private theorem counts_mono (xs : List U32) (i j d : Nat) (h : i ≤ j) :
    count xs i d ≤ count xs j d := by
  rw [show j = i + (j-i) by omega]
  simp [count,List.take_add,List.countP_append]

private theorem rank_window (xs : List U32) (i : Nat) (hi : i < xs.length) :
    below xs xs[i]!.val ≤ rank xs i ∧ rank xs i < below xs (xs[i]!.val+1) := by
  have h := counts_mono xs (i+1) xs.length xs[i]!.val (by omega)
  rw [nextCount _ _ _ hi,ite_eq_left rfl] at h
  simp only [rank,below_succ]; omega

private theorem rank_lt (xs : List U32) (i : Nat) (hi : i < xs.length) : rank xs i < xs.length :=
  (rank_window xs i hi).2.trans_le List.countP_le_length

private theorem rank_ne {xs : List U32} {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (ij : i < j) : rank xs i ≠ rank xs j := by
  have mono (a b : Nat) (h : a ≤ b) : below xs a ≤ below xs b :=
    List.countP_mono_left (by intro x _ h'; simp only [decide_eq_true_eq] at *; omega)
  have bi := rank_window xs i hi
  have bj := rank_window xs j hj
  rcases lt_trichotomy xs[i]!.val xs[j]!.val with lt | eq | gt
  · exact ne_of_lt (bi.2.trans_le ((mono _ _ (Nat.succ_le_of_lt lt)).trans bj.1))
  · have h := counts_mono xs (i+1) j xs[i]!.val (by omega)
    rw [nextCount _ _ _ hi,ite_eq_left rfl] at h
    simp only [rank,← eq]; omega
  · exact Ne.symm (ne_of_lt (bj.2.trans_le ((mono _ _ (Nat.succ_le_of_lt gt)).trans bi.1)))

private theorem set_self {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by rw [getElem!_pos _ _ (by simpa using hi),List.getElem_set_self]
private theorem set_ne {α} [Inhabited α] (xs : List α) (i j : Nat) (x : α) (h : i ≠ j) :
    (xs.set i x)[j]! = xs[j]! := by
  by_cases hj : j < xs.length
  · rw [getElem!_pos _ _ (by simpa using hj),getElem!_pos xs j hj,List.getElem_set_ne h]
  · rw [getElem!_neg (xs.set i x) j (by simp [hj]),getElem!_neg xs j hj]

private theorem histogram (xs : Slice U32) (len : xs.length ≤ 67)
    (small : ∀ i < xs.length, xs.val[i]!.val < 16) :
    chain_order_loop0 ⟨xs,0⟩ (Array.repeat 16#usize 0#usize) ⦃ v =>
      ∀ d < 16, v.val[d]!.val = count xs.val xs.length d ⦄ := by
  unfold chain_order_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.slice.iter.Iter U32 × Array Usize 16#usize => xs.length-q.1.i)
    (inv := fun q => q.1.slice=xs ∧ q.1.i ≤ xs.length ∧ ∀ d < 16, q.2.val[d]!.val = count xs.val q.1.i d)
  · rintro ⟨⟨ds,i⟩,v⟩ ⟨rfl,le,cnts⟩
    simp only at le cnts len small
    unfold chain_order_loop0.body core.slice.iter.IteratorSliceIter.next
    by_cases live : i < ds.length
    · have hi : i < ds.val.length := live
      have hl : i < ds.len.val := by simpa using live
      have hd := small i live
      have cast : (UScalar.cast .Usize ds[i]).val = ds.val[i]!.val := by
        rw [UScalar.cast_val_eq, getElem!_pos ds.val i hi, Nat.mod_eq_of_lt (by scalar_tac)]
        rfl
      simp only [dite_eq_left hl,bind_ok,lift]
      step as ⟨x,hx⟩
      have old : x.val = count ds.val i ds.val[i]!.val := by
        rw [hx,← getElem!_pos]; erw [cast,cnts _ hd]
      have bound : count ds.val i ds.val[i]!.val ≤ ds.length :=
        List.countP_le_length.trans (by simp [Slice.length])
      step as ⟨v',hv'⟩
      step as ⟨a,ha⟩
      refine ⟨by omega,?_,by omega⟩
      intro d h
      rw [nextCount _ _ _ hi,ha,Array.set_val_eq]; erw [cast]
      by_cases eq : ds.val[i]!.val=d
      · subst d; rw [set_self _ _ _ (by simpa using hd), hv',old,ite_eq_left rfl]
      · rw [set_ne _ _ _ _ eq,cnts _ h,ite_eq_right eq,Nat.add_zero]
    · have hl : ¬ i < ds.len.val := by simpa using live
      simp only [dite_eq_right hl,step_simps]
      have eq : i = ds.length := by omega
      exact eq ▸ cnts
  · refine ⟨rfl,Nat.zero_le _,?_⟩
    intro d hd
    rw [Array.repeat_val, getElem!_pos (List.replicate _ _) d (by simpa using hd), List.getElem_replicate]; rfl

private abbrev Iter := core.slice.iter.IterMut Usize

private theorem offsets (xs : List U32) (len : xs.length ≤ 67)
    (cs : Slice Usize) (size : cs.length = 16) (counts : ∀ d < 16, cs.val[d]!.val = count xs xs.length d) :
    chain_order_loop1 ⟨cs,0⟩ id 0#usize ⦃ r =>
      (r.2 r.1).slice.length = 16 ∧ ∀ d < 16, (r.2 r.1).slice.val[d]!.val = below xs d ⦄ := by
  unfold chain_order_loop1
  apply loop.spec_decr_nat
    (measure := fun q : Iter × (Iter → Iter) × Usize => 16-q.1.i)
    (inv := fun q => q.1.slice=cs ∧ q.1.i≤16 ∧ q.2.2.val=below xs q.1.i ∧
      ∀ next : Iter, next.slice.length = 16 →
        (q.2.1 next).slice.length=16 ∧ (∀ j < q.1.i,(q.2.1 next).slice.val[j]!.val=below xs j) ∧
        (∀ j, q.1.i ≤ j → j < 16 → (q.2.1 next).slice.val[j]! = next.slice.val[j]!))
  · rintro ⟨it,back,start⟩ ⟨hs,hi,hstart,restore⟩
    simp only at hs hi hstart restore ⊢
    unfold chain_order_loop1.body
    apply WP.spec_bind (core.slice.iter.IteratorIterMut.next.spec it)
    rintro ⟨o,it',undo⟩ ⟨same,none,status⟩
    cases o with
    | none =>
      obtain ⟨length,done,_⟩ := restore it' (by rw [same,hs,size])
      simp only [none, WP.spec_ok,uncurry]
      refine ⟨length,fun j hj => done j ?_⟩
      rw [hs,size] at status; omega
    | some y =>
      obtain ⟨live,rfl,adv,insert⟩ := status
      have hlt : it.i<16 := by rwa [hs,size] at live
      have add : start.val+it.slice.val[it.i]!.val = below xs (it.i+1) := by
        rw [hs,counts _ hlt,hstart,below_succ]
      have cap : below xs (it.i+1) ≤ xs.length := List.countP_le_length
      simp only [uncurry]
      step as ⟨next,hnew⟩
      refine ⟨same.trans hs,by omega,by rw [adv,← add,hnew],fun nextIt hl => ?_,by omega⟩
      rw [insert]
      obtain ⟨length,done,keep⟩ := restore {slice:=nextIt.slice.setAtNat it.i start,i:=nextIt.i} (by simp [hl])
      have wrote := fun j => Slice.getElem!_Nat_setAtNat nextIt.slice it.i j start (by simpa [hl] using hlt)
      refine ⟨length,fun j hj => ?_, fun j hj hj' => ?_⟩
      · by_cases eq : j=it.i
        · subst j; rw [keep _ (by omega) hlt,wrote]; simpa using hstart
        · exact done j (by omega)
      · rw [keep j (by omega) hj',wrote]; simp [show j ≠ it.i by omega]
  · exact ⟨rfl,Nat.zero_le _,by simp [below],fun it hi => ⟨hi,by simp,by simp⟩⟩

private theorem scatter (xs : Slice U32) (len : xs.length ≤ 67)
    (small : ∀ i < xs.length, xs.val[i]!.val < 16) (offs : Array Usize 16#usize)
    (offset : ∀ d < 16, offs.val[d]!.val = below xs.val d) :
    chain_order_loop2 ⟨⟨xs,0⟩,0#usize⟩ offs (Array.repeat 67#usize 0#usize) ⦃ order =>
      ∀ i < xs.length, order.val[rank xs.val i]!.val = i ⦄ := by
  unfold chain_order_loop2
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32) ×
      Array Usize 16#usize × Array Usize 67#usize => xs.length - q.1.iter.i)
    (inv := fun q => q.1.iter.slice = xs ∧ q.1.iter.i ≤ xs.length ∧ q.1.count.val=q.1.iter.i ∧
      (∀ d < 16, q.2.1.val[d]!.val = below xs.val d + count xs.val q.1.iter.i d) ∧
      ∀ k < q.1.iter.i, q.2.2.val[rank xs.val k]!.val = k)
  · rintro ⟨⟨⟨ds,i⟩,cnt⟩,v,ord⟩ ⟨rfl,le,idx,cnts,prev⟩
    simp only at le idx cnts prev len small
    unfold chain_order_loop2.body core.iter.adapters.enumerate.IteratorEnumerate.next
      core.iter.traits.iterator.IteratorSliceIter core.slice.iter.IteratorSliceIter.next
    by_cases live : i < ds.length
    · have sz : i < ds.val.length := live
      have hl : i < ds.len.val := by simpa using live
      simp only [dite_eq_left hl,bind_ok]
      have room : cnt.val+1 ≤ Usize.max := by scalar_tac
      step as ⟨next,hnext⟩
      simp only [lift]
      have digit := small i live
      have cast : (UScalar.cast .Usize ds[i]).val = ds.val[i]!.val := by
        rw [UScalar.cast_val_eq,getElem!_pos ds.val i sz,Nat.mod_eq_of_lt (by scalar_tac)]; rfl
      step as ⟨slot,back,hs,hb⟩
      have pos : slot.val = rank ds.val i := by
        rw [hs,← getElem!_pos]; erw [cast,cnts _ digit]; rfl
      have bound : slot.val < 67 := lt_of_lt_of_le (pos ▸ rank_lt ds.val i sz) len
      step as ⟨ord',hwrite⟩
      step as ⟨slot',hadd⟩
      refine ⟨by omega,by omega,?_,?_,by omega⟩
      · intro d hd
        rw [hb,Array.set_val_eq,nextCount _ _ _ sz]; erw [cast]
        by_cases eq : ds.val[i]!.val=d
        · subst d; rw [set_self _ _ _ (by simpa using digit),hadd,pos,ite_eq_left rfl]; simp [rank,Nat.add_assoc]
        · rw [set_ne _ _ _ _ eq,cnts _ hd,ite_eq_right eq,Nat.add_zero]
      · intro k hk
        rw [hwrite,Array.set_val_eq,pos]
        by_cases eq : k = i
        · subst k; rw [set_self _ _ _ (by rw [← pos]; simpa using bound),idx]
        · rw [set_ne _ _ _ _ (Ne.symm (rank_ne (by omega) sz (by omega)))]; exact prev k (by omega)
    · have hl : ¬i < ds.len.val := by simpa using live
      simp only [dite_eq_right hl,bind_ok,step_simps]
      have eq : i=ds.length := by omega
      exact eq ▸ prev
  · simp only
    exact ⟨trivial,Nat.zero_le _,rfl,by simpa [count] using offset,fun _ h => by omega⟩

/-- Every possible WOTS digit array is scheduled once per chain at its stable counting-sort rank. -/
theorem chain_order_spec (xs : Slice U32) (len : xs.length ≤ 67)
    (small : ∀ i < xs.length, xs.val[i]!.val < 16) :
    chain_order xs ⦃ order =>
      (∀ i < xs.length, rank xs.val i < xs.length ∧ order.val[rank xs.val i]!.val = i) ∧
      (∀ j < xs.length, ∃ i < xs.length, rank xs.val i = j ∧ order.val[j]!.val = i) ⦄ := by
  unfold chain_order
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  let* ⟨cs,hcs⟩ ← histogram xs len small
  simp only [MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,bind_ok]
  obtain ⟨⟨it,back⟩, pref, size, order⟩ := slhdsa.spec_imp_exists (offsets xs.val len cs.to_slice (by simp) (by simpa using hcs))
  change chain_order_loop1 ⟨cs.to_slice,0⟩ (fun im => im) 0#usize = ok (it,back) at pref
  simp only [uncurry,pref,bind_ok]
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
  let off := Array.from_slice cs (back it).slice
  have data : off.val = (back it).slice.val := Array.from_slice_val _ _ (by simpa using size)
  let* ⟨out,index⟩ ← scatter xs len small off (by rwa [data])
  let f : Fin xs.length → Fin xs.length := fun i => ⟨rank xs.val i.val,rank_lt _ _ i.isLt⟩
  have inj : Function.Injective f := by
    intro i j eq
    apply Fin.ext
    have same : rank xs.val i.val = rank xs.val j.val := congrArg Fin.val eq
    rcases lt_trichotomy i.val j.val with less | eq' | more
    · exact False.elim (rank_ne i.isLt j.isLt less same)
    · exact eq'
    · exact False.elim (rank_ne j.isLt i.isLt more same.symm)
  refine ⟨fun i hi => ⟨rank_lt _ _ hi,index i hi⟩, fun j hj => ?_⟩
  obtain ⟨i,e⟩ := (Finite.injective_iff_surjective.mp inj) ⟨j,hj⟩
  have he : rank xs.val i.val = j := congrArg Fin.val e
  exact ⟨i.val,i.isLt,he,he ▸ index i.val i.isLt⟩

end CacheopsRust.WotsOrder
