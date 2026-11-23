import Wots.Funs
import Chainwide.Counters
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512

abbrev Bins := Array Usize 16#usize
def frequency (xs : List U32) (k : Nat) := xs.countP (fun d => decide (d.val=k))
def below (xs : List U32) (k : Nat) := xs.countP (fun d => decide (d.val<k))

theorem frequency_le (xs : List U32) (k : Nat) : frequency xs k ≤ xs.length := List.countP_le_length

theorem histogram_spec (digits : Slice U32) (small : digits.length ≤ 67)
    (valid : ∀ i < digits.length, digits.val[i]!.val < 16) :
    recover_loop0 ⟨digits,0⟩ (Array.repeat 16#usize 0#usize) ⦃ counts =>
      ∀ k < 16, counts.val[k]!.val = frequency digits.val k ⦄ := by
  unfold recover_loop0
  apply loop.spec_decr_nat (measure := fun p : core.slice.iter.Iter U32 × Bins => digits.length-p.1.i)
    (inv := fun p => p.1.slice = digits ∧ p.1.i ≤ digits.length ∧
      ∀ k < 16, p.2.val[k]!.val = frequency (digits.val.take p.1.i) k)
  · rintro ⟨⟨s,i⟩,buf⟩ ⟨rfl,hi,old⟩
    simp only at hi old
    unfold recover_loop0.body core.slice.iter.IteratorSliceIter.next
    by_cases live : i < s.length
    · have hl : i < s.len.val := by simpa using live
      simp only [dif_pos hl,lift,bind_ok]
      let dig := s[i]
      have sameDig : s.val[i]! = dig := getElem!_pos s.val i live
      have hd : dig.val < 16 := sameDig ▸ valid i live
      let idx := UScalar.cast .Usize dig
      have idVal : idx.val = dig.val := by dsimp [idx]; scalar_tac
      have ix : (UScalar.cast .Usize s[i]).val = dig.val := by
        exact idVal
      step as ⟨value,hv⟩
      step as ⟨v,hv'⟩
      · have lim := frequency_le (s.val.take i) dig.val
        have e : value.val = frequency (s.val.take i) dig.val := by
          rw [hv,← getElem!_pos,ix]; exact old _ hd
        simp only [List.length_take] at lim; scalar_tac
      step as ⟨out,ho⟩
      refine ⟨by omega,?_,by omega⟩
      intro k hk
      change out.val[k]!.val = frequency (s.val.take (i+1)) k
      rw [List.take_succ_eq_append_getElem live]
      simp only [frequency,List.countP_append,List.countP_cons,List.countP_nil]
      rw [ho,Array.set_val_eq]
      rw [ix]
      by_cases same : k=dig.val
      · subst k
        rw [Avx2.setSame _ _ _ (by simp; omega),hv',hv,← getElem!_pos,ix,old _ hd]
        simp [dig,frequency]; rfl
      · rw [Avx2.setOther _ _ _ _ (Ne.symm same),old k hk]
        have ne : (s.val[i]'live).val ≠ k := Ne.symm same
        simp [ne,frequency]
    · have hl : ¬i<s.len.val := by simpa using live
      simp only [dif_neg hl,bind_ok,step_simps]
      have e : i=s.length := by omega
      simpa [e,Slice.length] using old
  · refine ⟨rfl,by simp,?_⟩
    intro k hk
    interval_cases k <;> rfl

theorem below_succ (xs : List U32) (k : Nat) : below xs (k+1) = below xs k + frequency xs k := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
    simp only [below,frequency,List.countP_cons] at *
    simp only [Nat.lt_succ_iff] at ih
    by_cases less : d.val<k
    · simp [less,show d.val<k+1 by omega,show d.val≠k by omega,ih]
      omega
    · by_cases eq : d.val=k
      · simp [less,eq,ih]; omega
      · simp [less,eq,show ¬d.val<k+1 by omega,ih]

theorem offsets_spec (digits : Slice U32) (counts : Bins) (small : digits.length ≤ 67)
    (hist : ∀ k < 16, counts.val[k]!.val = frequency digits.val k) :
    recover_loop1 ⟨1#usize,16#usize⟩ counts (Array.repeat 16#usize 0#usize) ⦃ offsets =>
      ∀ k < 16, offsets.val[k]!.val = below digits.val k ⦄ := by
  unfold recover_loop1
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Bins => 16-p.1.start.val)
    (inv := fun p => p.1.end = 16#usize ∧ 1 ≤ p.1.start.val ∧ p.1.start.val ≤ 16 ∧
      ∀ k < p.1.start.val, p.2.val[k]!.val = below digits.val k)
  · rintro ⟨it,a⟩ ⟨he,hs,hb,prior⟩
    simp only at he hs hb prior
    unfold recover_loop1.body
    by_cases more : it.start.val < 16
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more)
        as ⟨o,next,ho,hn,he'⟩
      simp only [ho]
      step as ⟨i,hi⟩
      step as ⟨offset,hv⟩
      step as ⟨count,hc⟩
      have eq : i.val+1=it.start.val := by scalar_tac
      have hval : offset.val+count.val = below digits.val it.start.val := by
        rw [hv,hc,← getElem!_pos,← getElem!_pos,prior _ (by omega),hist _ (by omega),← below_succ,eq]
      have cap : below digits.val it.start.val ≤ digits.length := List.countP_le_length
      step as ⟨updated,hu⟩
      step as ⟨b,hb'⟩
      refine ⟨he'.trans he,by omega,by omega,?_,by omega⟩
      intro k hk
      rw [hb',Array.set_val_eq]
      by_cases same : k=it.start.val
      · subst k; rw [Avx2.setSame _ _ _ (by simp; omega),hu,hval]
      · rw [Avx2.setOther _ _ _ _ (Ne.symm same),prior k (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; change 16 ≤ it.start.val; omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      exact fun k hk => prior _ (by omega)
  · refine ⟨rfl,by decide,by decide,?_⟩
    intro k hk
    have eq : k=0 := by change k<1 at hk; omega
    subst k
    simp [Array.repeat,below]

end slhdsa.X86.Wots
