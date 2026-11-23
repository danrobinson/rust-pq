import Leaf256.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open LeafRust.sha256.x86.avx512

theorem constants : ∀ i : Fin 64, (LeafRust.sha256.K.val[i.val]!).bv = Spec.SHA256.K[i.val]! := by
  unfold LeafRust.sha256.K Spec.SHA256.K
  decide

theorem first_two (iv : Array Reg 8#usize) (w : Array Reg 16#usize) (blocks : Fin 16 → Spec.Bytes)
    (hw : ∀ k, k < 2 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) :
    fors_leaves_loop0 ⟨0#usize,2#usize⟩ w iv ⦃ s =>
      Trace s (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 2 ⦄ := by
  unfold fors_leaves_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 8#usize => 2-p.1.start.val)
    (inv := fun p => p.1.end = 2#usize ∧ p.1.start.val ≤ 2 ∧
      Trace p.2 (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) p.1.start.val)
  · rintro ⟨it,s⟩ ⟨he,hi,ht⟩
    simp only at he hi ht
    unfold fors_leaves_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · have hsmall : it.start.val < 2 := by rw [he] at hlt; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨opt,nxt,hopt,hn,hen⟩
      simp only [hopt]
      step as ⟨v,hv⟩
      step as ⟨c,hc⟩
      have hconst := constants ⟨it.start.val,by omega⟩
      step with round_spec s v c (fun j => Spec.SHA256.schedule (blocks j)) it.start.val
        (by simpa only [hc,← getElem!_pos] using hconst)
        (fun j => by rw [hv, ← getElem!_pos, hw _ (by omega), slhdsa.schedule_lt16 _ _ (by omega)]) as ⟨s',hs⟩
      refine ⟨hen.trans he, by omega, fun j => ?_, by omega⟩
      rw [hs,ht,hn,List.range_succ,List.foldl_append]; rfl
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨opt,nxt,hopt,hn⟩
      simp only [hopt,step_simps]
      have h : it.start.val = 2 := by rw [he] at hlt; change ¬it.start.val < 2 at hlt; omega
      exact h ▸ ht
  · simp [Trace]

end slhdsa.X86.Leaf
