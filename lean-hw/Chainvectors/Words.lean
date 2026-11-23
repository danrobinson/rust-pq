import Chainvectors.Save
import Leaf256.Messages
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainVectorRust.sha256.x86.avx512
open _root_.core.core_arch.x86.avx512f

def addressWord (old : Nat → BitVec 32) (fixed counter : BitVec 32) (k : Nat) :=
  if k = 4 then fixed ||| (counter >>> 16) else
  if k = 5 then (counter <<< 16) ||| (old 5 &&& 0xffff) else old k

theorem address_spec (w : Array Reg 16#usize) (fixed counter : Reg) :
    chain_address w fixed counter (fun _ => 0xffff) ⦃ out => ∀ k, k < 16 → ∀ j,
      out.val[k]! j = addressWord (fun t => w.val[t]! j) (fixed j) (counter j) k ⦄ := by
  unfold chain_address
  simp only [_mm512_srli_epi32,ChainVectorRust.core.core_arch.x86.avx512f._mm512_slli_epi32,
    ChainVectorRust.core.core_arch.x86.avx512f._mm512_and_si512,ChainVectorRust.core.core_arch.x86.avx512f._mm512_or_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_and_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,bind_ok]
  step*
  have fifth : mi3 = w.val[5]! := by
    rw [mi3_post,← getElem!_pos,words1_post,Array.set_val_eq]
    exact Avx2.setOther _ _ _ _ (by decide)
  simp only [out_post,words1_post,Array.set_val_eq,show (4#usize).val = 4 by rfl,
    show (5#usize).val = 5 by rfl,fifth]
  interval_cases k <;> simp (disch := decide) only [addressWord,↓reduceIte,Avx2.setOther]
  all_goals first | rfl | (rw [Avx2.setSame _ _ _ (by simp)]; rfl)

def valueWord (old hash : Nat → BitVec 32) (n k : Nat) :=
  if k = 5 then hash 0 >>> 16
  else if k = 5+n/4 then (hash (n/4-1) <<< 16) ||| (old k &&& 0xffff)
  else if 6 ≤ k ∧ k < 5+n/4 then Leaf.interior (hash (k-6)) (hash (k-5))
  else old k

theorem interior_spec (w : Array Reg 16#usize) (hash : Array Reg 8#usize) (limit : Usize)
    (lo : 1 ≤ limit.val) (hi : limit.val ≤ 8) :
    chain_value_loop ⟨1#usize,limit⟩ w hash ⦃ out =>
      ∀ k, k < 16 → ∀ j : Fin 16, out.val[k]! j =
        if 6 ≤ k ∧ k < 5+limit.val then Leaf.interior (hash.val[k-6]! j) (hash.val[k-5]! j)
        else w.val[k]! j ⦄ := by
  unfold chain_value_loop
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Array Reg 16#usize =>
    limit.val-p.1.start.val)
    (inv := fun p => p.1.end = limit ∧ 1 ≤ p.1.start.val ∧ p.1.start.val ≤ limit.val ∧
      ∀ k, k < 16 → ∀ j : Fin 16, p.2.val[k]! j = if 6 ≤ k ∧ k < 5+p.1.start.val then
        Leaf.interior (hash.val[k-6]! j) (hash.val[k-5]! j) else w.val[k]! j)
  · rintro ⟨it,a⟩ ⟨he,hl,hb,ha⟩
    simp only at he hl hb ha
    unfold chain_value_loop.body
    by_cases hlt : it.start.val < it.end.val
    · have h : it.start.val < limit.val := he ▸ hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt as ⟨o,next,ho,hn,hend⟩
      simp only [ho,_mm512_srli_epi32,ChainVectorRust.core.core_arch.x86.avx512f._mm512_slli_epi32,
        ChainVectorRust.core.core_arch.x86.avx512f._mm512_or_si512,LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,
        LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,bind_ok]
      step*
      refine ⟨hend.trans he,by omega,by omega,?_,by omega⟩
      intro k hk j
      rw [a_post,Array.set_val_eq]
      by_cases eq : k = 5+it.start.val
      · subst k
        rw [show 5+it.start.val = i2.val by omega,Avx2.setSame _ _ _ (by scalar_tac)]
        rw [if_pos (by omega),show i2.val - 6 = i1.val by omega,show i2.val - 5 = it.start.val by omega]
        simp only [mi_post,mi2_post,Leaf.interior]
        simp (disch := scalar_tac) only [getElem!_pos]; rfl
      · rw [Avx2.setOther _ _ _ _ (by omega),ha k hk j]
        split_ifs <;> first | rfl | omega
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,hn⟩
      simp only [ho,step_simps]
      have eq : it.start.val = limit.val := by rw [he] at hlt; omega
      simpa only [eq] using ha
  · simp [lo]


theorem value_spec (N : Usize) (w : Array Reg 16#usize) (hash : Array Reg 8#usize)
    (shape : N.val = 16 ∨ N.val = 24 ∨ N.val = 32) :
    chain_value N w hash (fun _ => 0xffff) ⦃ out => ∀ k, k < 16 → ∀ j,
      out.val[k]! j = valueWord (fun t => w.val[t]! j) (fun t => hash.val[t]! j) N.val k ⦄ := by
  unfold chain_value
  simp only [_mm512_srli_epi32,ChainVectorRust.core.core_arch.x86.avx512f._mm512_slli_epi32,
    ChainVectorRust.core.core_arch.x86.avx512f._mm512_and_si512,ChainVectorRust.core.core_arch.x86.avx512f._mm512_or_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_and_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,bind_ok]
  step as ⟨first,hf⟩
  step as ⟨a,ha⟩
  step as ⟨lim,hl⟩
  have bounds : 1 ≤ lim.val ∧ lim.val ≤ 8 := by omega
  step with interior_spec a hash lim (by omega) (by omega) as ⟨middle,hm⟩
  step as ⟨last,hn⟩
  step as ⟨h,hh⟩
  step as ⟨pos,hpos⟩
  step as ⟨wlast,hwl⟩
  step as ⟨pos',hp'⟩
  step as ⟨out,ho⟩
  rename_i k hk j
  have av (i : Nat) (hi : i < 16) : a.val[i]! j =
      if i=5 then hash.val[0]! j >>> 16 else w.val[i]! j := by
    rw [ha,Array.set_val_eq,show (5#usize).val = 5 by rfl]
    by_cases e : i=5
    · subst i; rw [Avx2.setSame _ _ _ (by simp),if_pos rfl,hf,← getElem!_pos]; rfl
    · rw [Avx2.setOther _ _ _ _ (Ne.symm e),if_neg e]
  have wl : wlast j = w.val[pos.val]! j := by
    rw [hwl,← getElem!_pos,hm _ (by omega),if_neg (by omega),av _ (by omega),if_neg (by omega)]
  rw [ho,Array.set_val_eq]
  by_cases e : k=pos'.val
  · subst k
    rw [Avx2.setSame _ _ _ (by scalar_tac),wl,hh,← getElem!_pos]
    simp (disch := omega) only [valueWord,if_neg (show pos'.val ≠ 5 by omega),if_pos (show pos'.val = 5+N.val/4 by omega)]
    rw [show last.val = N.val/4-1 by omega,show pos.val=pos'.val by omega]; rfl
  · rw [Avx2.setOther _ _ _ _ (Ne.symm e),hm k hk j]
    by_cases mid : 6 ≤ k ∧ k < 5+lim.val
    · rw [if_pos mid]
      simp only [valueWord,if_neg (show k ≠ 5 by omega),if_neg (show k ≠ 5+N.val/4 by omega),if_pos (show 6 ≤ k ∧ k < 5+N.val/4 by omega)]
    · rw [if_neg mid,av k hk]
      simp (disch := omega) only [valueWord,if_neg (show k ≠ 5+N.val/4 by omega),if_neg (show ¬(6 ≤ k ∧ k < 5+N.val/4) by omega)]

end slhdsa.X86.Chain
