import Leaf256.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open LeafRust.sha256.x86.avx512
open LeafRust.core.core_arch.x86.avx512f
open _root_.core.core_arch.x86.avx512f

/-- The unaligned PRF digest starts in the low half of word five. Each interior
word gets the low half of one digest word and the high half of the next. -/
def interior (a b : BitVec 32) := (a <<< 16) ||| (b >>> 16)

theorem interior_bytes (a b c d e f g h : BitVec 8) :
    interior (a ++ b ++ c ++ d) (e ++ f ++ g ++ h) = c ++ d ++ e ++ f := by
  unfold interior
  bv_decide

theorem pack_words (w : Array Reg 16#usize) (prf : Array Reg 8#usize) (limit : Usize)
    (lo : 1 ≤ limit.val) (hi : limit.val ≤ 8) :
    fors_leaves_loop1_loop0 ⟨1#usize,limit⟩ w prf ⦃ out =>
      ∀ k, k < 16 → ∀ j : Fin 16, out.val[k]! j =
        if 6 ≤ k ∧ k < 5+limit.val then interior (prf.val[k-6]! j) (prf.val[k-5]! j)
        else w.val[k]! j ⦄ := by
  unfold fors_leaves_loop1_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 16#usize =>
    limit.val-p.1.start.val)
    (inv := fun p => p.1.end = limit ∧ 1 ≤ p.1.start.val ∧ p.1.start.val ≤ limit.val ∧
      ∀ k, k < 16 → ∀ j : Fin 16, p.2.val[k]! j = if 6 ≤ k ∧ k < 5+p.1.start.val then
        interior (prf.val[k-6]! j) (prf.val[k-5]! j) else w.val[k]! j)
  · rintro ⟨it,a⟩ ⟨he,hl,hb,ha⟩
    simp only at he hl hb ha
    unfold fors_leaves_loop1_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · have h : it.start.val < limit.val := he ▸ hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨o,next,ho,hn,hend⟩
      simp only [ho,_mm512_slli_epi32,_mm512_srli_epi32,_mm512_or_si512,bind_ok]
      step*
      refine ⟨hend.trans he,by omega,by omega,?_,by omega⟩
      intro k hk j
      rw [a_post,Array.set_val_eq]
      by_cases eq : k = 5+it.start.val
      · subst k
        rw [show 5+it.start.val = i1.val by omega,Avx2.setSame _ _ _ (by scalar_tac)]
        rw [if_pos (by omega),show i1.val - 6 = i.val by omega,show i1.val - 5 = it.start.val by omega]
        simp only [mi_post,mi2_post,interior]
        simp (disch := scalar_tac) only [getElem!_pos]; rfl
      · rw [Avx2.setOther _ _ _ _ (by omega),ha k hk j]
        split_ifs <;> first | rfl | omega
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,hn⟩
      simp only [ho,step_simps]
      have eq : it.start.val = limit.val := by rw [he] at hlt; omega
      simpa only [eq] using ha
  · simp [lo]

end slhdsa.X86.Leaf
