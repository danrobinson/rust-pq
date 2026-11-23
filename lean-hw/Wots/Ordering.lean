import Wots.Histogram
import Mathlib.Data.Fintype.Card
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512

/-- The stable counting-sort position of the signature element at index i. -/
def rank (xs : List U32) (i : Nat) :=
  below xs xs[i]!.val + frequency (xs.take i) xs[i]!.val

private theorem freq_take_mono (xs : List U32) (k i j : Nat) (le : i ≤ j) :
    frequency (xs.take i) k ≤ frequency (xs.take j) k := by
  have h := List.take_append_drop i (xs.take j)
  have e := congrArg (fun l => frequency l k) h
  simp only [frequency,List.countP_append,List.take_take,Nat.min_eq_left le] at e ⊢
  omega

theorem frequency_next (xs : List U32) (k i : Nat) (hi : i < xs.length) :
    frequency (xs.take (i+1)) k = frequency (xs.take i) k + (if xs[i]!.val = k then 1 else 0) := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [frequency,List.countP_append,List.countP_cons,List.countP_nil,decide_eq_true_eq,Nat.zero_add]
  rw [getElem!_pos xs i hi]

private theorem below_mono (xs : List U32) {a b : Nat} (h : a ≤ b) : below xs a ≤ below xs b := by
  induction h with
  | refl => rfl
  | step h ih => rw [below_succ]; omega

theorem rank_range (xs : List U32) (i : Nat) (hi : i < xs.length) :
    below xs xs[i]!.val ≤ rank xs i ∧ rank xs i < below xs (xs[i]!.val+1) := by
  have le := freq_take_mono xs xs[i]!.val (i+1) xs.length (by omega)
  rw [List.take_length,frequency_next _ _ _ hi,if_pos rfl] at le
  unfold rank
  rw [below_succ]
  omega

theorem rank_bound (xs : List U32) (i : Nat) (hi : i < xs.length) : rank xs i < xs.length :=
  Nat.lt_of_lt_of_le (rank_range xs i hi).2 List.countP_le_length

theorem rank_injective (xs : List U32) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length)
    (eq : rank xs i = rank xs j) : i = j := by
  obtain ⟨il,iu⟩ := rank_range xs i hi
  obtain ⟨jl,ju⟩ := rank_range xs j hj
  have digit : xs[i]!.val = xs[j]!.val := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le iu ((below_mono xs (Nat.succ_le_of_lt lt)).trans jl))) eq
    · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le ju ((below_mono xs (Nat.succ_le_of_lt gt)).trans il))) eq.symm
  unfold rank at eq
  rw [digit] at eq
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|gt
  · have h := freq_take_mono xs xs[j]!.val (i+1) j lt
    rw [frequency_next _ _ _ hi,if_pos digit] at h; omega
  · have h := freq_take_mono xs xs[j]!.val (j+1) i gt
    rw [frequency_next _ _ _ hj,if_pos rfl] at h; omega


abbrev Enum := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U32)
abbrev Order := Array Usize 67#usize

theorem order_spec (digits : Slice U32) (offsets : Bins) (initial : Order) (small : digits.length ≤ 67)
    (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (start : ∀ k < 16, offsets.val[k]!.val = below digits.val k) :
    recover_loop2 ⟨⟨digits,0⟩,0#usize⟩ offsets initial ⦃ order =>
      ∀ i < digits.length, order.val[rank digits.val i]!.val = i ⦄ := by
  unfold recover_loop2
  apply loop.spec_decr_nat (measure := fun p : Enum × Bins × Order => digits.length-p.1.iter.i)
    (inv := fun p => p.1.iter.slice = digits ∧ p.1.count.val = p.1.iter.i ∧ p.1.iter.i ≤ digits.length ∧
      (∀ k < 16, p.2.1.val[k]!.val = below digits.val k + frequency (digits.val.take p.1.iter.i) k) ∧
      ∀ j < p.1.iter.i, p.2.2.val[rank digits.val j]!.val = j)
  · rintro ⟨⟨⟨s,i⟩,count⟩,cursor,order⟩ ⟨rfl,hcount,hi,hcursor,prev⟩
    simp only at hcount hi hcursor prev small valid
    unfold recover_loop2.body core.iter.adapters.enumerate.IteratorEnumerate.next
    simp only [core.iter.traits.iterator.IteratorSliceIter,core.slice.iter.IteratorSliceIter.next]
    by_cases live : i < s.length
    · have hl : i < s.len.val := by simpa using live
      simp only [dif_pos hl,lift,bind_ok]
      step as ⟨next,hn⟩
      let d := s.val[i]!.val
      have hd : d < 16 := valid i live
      have eqDigit : s[i].val = d := by change _ = s.val[i]!.val; rw [getElem!_pos s.val i live]; rfl
      have cast : (UScalar.cast .Usize s[i]).val = d := by rw [← eqDigit]; scalar_tac
      step as ⟨pos,hpos⟩
      have posOK : pos.val = rank s.val i := by rw [hpos,← getElem!_pos,cast,hcursor _ hd]; rfl
      have len : s.val.length = s.length := rfl
      have bound := rank_bound s.val i live
      step as ⟨written,hw⟩
      step as ⟨loc,hloc⟩
      have here : loc.val = rank s.val i := by rw [hloc,← getElem!_pos,cast,hcursor _ hd]; rfl
      step as ⟨succ,hs⟩
      step as ⟨cur,hc⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · omega
      · omega
      · intro k hk
        rw [hc,Array.set_val_eq,cast,frequency_next _ _ _ live]
        by_cases same : k=d
        · subst k
          rw [Avx2.setSame _ _ _ (by simp; omega),hs,here,if_pos rfl]
          dsimp only [rank,d]
          omega
        · rw [Avx2.setOther _ _ _ _ (Ne.symm same),hcursor _ hk,if_neg (Ne.symm same),Nat.add_zero]
      · intro j hj
        rw [hw,Array.set_val_eq,posOK]
        by_cases same : j=i
        · subst j; rw [Avx2.setSame _ _ _ (by simp; omega),hcount]
        · have ne : rank s.val i ≠ rank s.val j := fun eq => same (rank_injective _ _ _ live (by omega) eq).symm
          rw [Avx2.setOther _ _ _ _ ne,prev _ (by omega)]
      · omega
    · have hl : ¬ i < s.len.val := by simpa using live
      simp only [dif_neg hl,bind_ok,step_simps]
      exact fun j hj => prev j (by omega)
  · simp [frequency]; simpa only [List.getElem!_eq_getElem?_getD] using start


theorem order_at (digits : Slice U32) (order : Order)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (pos : Nat) (live : pos < digits.length) :
    order.val[pos]!.val < digits.length ∧ rank digits.val order.val[pos]!.val = pos := by
  let f (i : Fin digits.length) : Fin digits.length := ⟨rank digits.val i.val,rank_bound _ _ i.isLt⟩
  have injective : Function.Injective f := fun i j eq =>
    Fin.ext (rank_injective _ _ _ i.isLt j.isLt (congrArg Fin.val eq))
  obtain ⟨i,hi⟩ := Finite.surjective_of_injective injective ⟨pos,live⟩
  have rankEq : rank digits.val i.val = pos := congrArg Fin.val hi
  have read := ordered i.val i.isLt
  rw [rankEq] at read
  rw [read]
  exact ⟨i.isLt,rankEq⟩

theorem workload_eq (digits : Slice U32) (valid : ∀ i < digits.length, digits.val[i]!.val < 16) :
    digits.length - frequency digits.val 15 = below digits.val 15 := by
  have full : below digits.val 16 = digits.length := by
    unfold below
    apply List.countP_eq_length.mpr
    intro x hx
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hx
    rw [← eq,decide_eq_true_eq,← getElem!_pos digits.val i hi]
    exact valid i hi
  rw [show 16=15+1 by decide,below_succ] at full
  omega

/-- Positions before the workload boundary need a chain step. Every position
after it contains a digit-15 endpoint ready for a direct copy. -/
theorem order_partition (digits : Slice U32) (order : Order)
    (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (pos : Nat) (live : pos < digits.length) :
    let i := order.val[pos]!.val
    i < digits.length ∧ (pos < digits.length-frequency digits.val 15 ↔ digits.val[i]!.val < 15) ∧
      (digits.length-frequency digits.val 15 ≤ pos ↔ digits.val[i]!.val = 15) := by
  dsimp only
  obtain ⟨hi,hr⟩ := order_at digits order ordered pos live
  let d := digits.val[order.val[pos]!.val]!.val
  have bound : d < 16 := valid _ hi
  have range := rank_range digits.val _ hi
  rw [hr] at range
  change below digits.val d ≤ pos ∧ pos < below digits.val (d+1) at range
  rw [workload_eq digits valid]
  change _ ∧ (pos < below digits.val 15 ↔ d < 15) ∧ (below digits.val 15 ≤ pos ↔ d=15)
  by_cases short : d < 15
  · have lt := Nat.lt_of_lt_of_le range.2 (below_mono digits.val (show d+1 ≤ 15 by omega))
    exact ⟨hi,by omega,by omega⟩
  · have eq : d=15 := by omega
    rw [eq] at range ⊢
    exact ⟨hi,by omega,by omega⟩

end slhdsa.X86.Wots
