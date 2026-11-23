import Chainvectors.Funs
import Leaf256.Pack
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open ChainVectorRust.sha256.x86.avx512
open ChainVectorRust.core.core_arch.x86.avx512f

theorem saved_spec (N : Usize) (old hash : Array Reg 8#usize) (mask : U16) (bound : N.val ≤ 32) :
    chain_done N old hash mask ⦃ out => ∀ k, k < 8 → ∀ j,
      out.val[k]! j = if k < N.val/4 ∧ mask.bv.getLsbD j.val then hash.val[k]! j else old.val[k]! j ⦄ := by
  unfold chain_done
  step as ⟨limit,hl⟩
  unfold chain_done_loop
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 8#usize => limit.val-p.1.start.val)
    (inv := fun p => p.1.end = limit ∧ p.1.start.val ≤ limit.val ∧ ∀ k, k < 8 → ∀ j,
      p.2.val[k]! j = if k < p.1.start.val ∧ mask.bv.getLsbD j.val then hash.val[k]! j else old.val[k]! j)
  · rintro ⟨it,saved⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold chain_done_loop.body
    by_cases lt : it.start.val < it.end.val
    · have hk : it.start.val < 8 := by rw [he] at lt; omega
      step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hn,hend⟩
      simp only [ho,_mm512_mask_mov_epi32,bind_ok]
      step*
      refine ⟨hend.trans he,by rw [he] at lt; omega,?_,by rw [he] at lt; omega⟩
      intro k h8 j
      rw [a_post,Array.set_val_eq]
      by_cases same : k = it.start.val
      · subst k
        rw [Avx2.setSame _ _ _ (by scalar_tac),mi_post,mi1_post,← getElem!_pos,← getElem!_pos,h _ hk j]
        simp [hn]
      · rw [Avx2.setOther _ _ _ _ (Ne.symm same),h k h8 j]
        have eq : k < next.start.val ↔ k < it.start.val := by omega
        simp only [eq]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = N.val/4 := by rw [he] at lt; omega
      simpa only [eq] using h
  · simp

end slhdsa.X86.Chain
