import Streamscalar.Init
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

theorem feed256 (st v : Array U32 8#usize) :
    StreamScalarRust.sha256.stream.scalar_loop0_loop0 ⟨0#usize,8#usize⟩ st v ⦃ out =>
      ∀ k < 8, out.val[k]!.bv = st.val[k]!.bv + v.val[k]!.bv ⦄ := by
  unfold StreamScalarRust.sha256.stream.scalar_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array U32 8#usize => 8-p.1.start.val)
    (inv := fun p => p.1.end = 8#usize ∧ p.1.start.val ≤ 8 ∧ ∀ k < 8,
      p.2.val[k]!.bv = if k < p.1.start.val then st.val[k]!.bv + v.val[k]!.bv else st.val[k]!.bv)
  · rintro ⟨it,a⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    unfold StreamScalarRust.sha256.stream.scalar_loop0_loop0.body
    by_cases more : it.start.val < 8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more)
        as ⟨o,t,ho,hn,he'⟩
      simp only [ho]
      step as ⟨x,hx⟩
      step as ⟨y,hy⟩
      step as ⟨z,hz⟩
      step as ⟨out,write⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro k hk
      rw [write,Array.set_val_eq]
      by_cases same : it.start.val = k
      · subst k
        have curr := prior it.start.val more
        simp only [Nat.lt_irrefl,ite_false] at curr
        simp (disch := scalar_tac) [getElem!_pos] at curr ⊢
        simp_all [List.getElem_set]
      · have cond : (k < t.start.val) = (k < it.start.val) := by apply propext; constructor <;> intro h <;> omega
        simpa (disch := scalar_tac) [getElem!_pos,List.getElem_set,same,cond] using prior k hk
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro k hk
      simpa [show k < it.start.val by omega] using prior k hk
  · exact ⟨rfl,by change 0 ≤ 8; decide,by simp⟩

theorem feed512 (st v : Array U64 8#usize) :
    StreamScalarRust.sha512.stream.scalar_loop0_loop0 ⟨0#usize,8#usize⟩ st v ⦃ out =>
      ∀ k < 8, out.val[k]!.bv = st.val[k]!.bv + v.val[k]!.bv ⦄ := by
  unfold StreamScalarRust.sha512.stream.scalar_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array U64 8#usize => 8-p.1.start.val)
    (inv := fun p => p.1.end = 8#usize ∧ p.1.start.val ≤ 8 ∧ ∀ k < 8,
      p.2.val[k]!.bv = if k < p.1.start.val then st.val[k]!.bv + v.val[k]!.bv else st.val[k]!.bv)
  · rintro ⟨it,a⟩ ⟨he,hb,prior⟩
    simp only at he hb prior
    unfold StreamScalarRust.sha512.stream.scalar_loop0_loop0.body
    by_cases more : it.start.val < 8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more)
        as ⟨o,t,ho,hn,he'⟩
      simp only [ho]
      step as ⟨x,hx⟩
      step as ⟨y,hy⟩
      step as ⟨z,hz⟩
      step as ⟨out,write⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro k hk
      rw [write,Array.set_val_eq]
      by_cases same : it.start.val = k
      · subst k
        have curr := prior it.start.val more
        simp only [Nat.lt_irrefl,ite_false] at curr
        simp (disch := scalar_tac) [getElem!_pos] at curr ⊢
        simp_all [List.getElem_set]
      · have cond : (k < t.start.val) = (k < it.start.val) := by apply propext; constructor <;> intro h <;> omega
        simpa (disch := scalar_tac) [getElem!_pos,List.getElem_set,same,cond] using prior k hk
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro k hk
      simpa [show k < it.start.val by omega] using prior k hk
  · exact ⟨rfl,by change 0 ≤ 8; decide,by simp⟩

end slhdsa.X86.Stream
