import Leaf256.Block
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open LeafRust.sha256.x86.avx512
open _root_.core.core_arch.x86.avx512f
open LeafRust.core.core_arch.x86.avx512f
open Spec.SHA256

def prfMessage (base : Array Reg 16#usize) (idx half : Reg) : Result (Array Reg 16#usize × Reg) := do
  let mi1 ← Array.index_usize base 4#usize
  let mi2 ← _mm512_srli_epi32 16#u32 idx
  let mi3 ← _mm512_or_si512 mi1 mi2
  let base1 ← Array.update base 4#usize mi3
  let high ← _mm512_slli_epi32 16#u32 idx
  let mi4 ← Array.index_usize base1 5#usize
  let mi5 ← _mm512_and_si512 mi4 half
  let mi6 ← _mm512_or_si512 high mi5
  let base2 ← Array.update base1 5#usize mi6
  ok (base2,high)

def leafMessage (N : Usize) (base2 : Array Reg 16#usize) (high half change : Reg)
    (prf : Array Reg 8#usize) : Result (Array Reg 16#usize) := do
  let mi7 ← Array.index_usize base2 2#usize
  let mi8 ← _mm512_xor_si512 mi7 change
  let base3 ← Array.update base2 2#usize mi8
  let mi9 ← Array.index_usize prf 0#usize
  let mi10 ← _mm512_srli_epi32 16#u32 mi9
  let mi11 ← _mm512_or_si512 high mi10
  let a ← Array.update base3 5#usize mi11
  let i6 ← N / 4#usize
  let w ←
    fors_leaves_loop1_loop0
    { start := 1#usize, «end» := i6 } a prf
  let i7 ← i6 - 1#usize
  let mi12 ← Array.index_usize prf i7
  let mi13 ← _mm512_slli_epi32 16#u32 mi12
  let i8 ← 5#usize + i6
  let mi14 ← Array.index_usize w i8
  let mi15 ← _mm512_and_si512 mi14 half
  let mi16 ← _mm512_or_si512 mi13 mi15
  let i9 ← 5#usize + i6
  let w1 ← Array.update w i9 mi16
  ok w1

theorem prf_message_spec (base : Array Reg 16#usize) (idx : Reg) :
    prfMessage base idx (fun _ => 0xffff) ⦃ w high => (∀ j, high j = idx j <<< 16) ∧
      ∀ k, k < 16 → ∀ j, w.val[k]! j = prfWords (fun i => base.val[i]! j) (idx j) k ⦄ := by
  unfold prfMessage
  simp only [_mm512_srli_epi32,_mm512_slli_epi32,_mm512_or_si512,_mm512_and_si512,bind_ok]
  step*
  refine ⟨fun _ => rfl,?_⟩
  intro k hk j
  have mi4eq : mi4 = base.val[5]! := by
    rw [mi4_post,← getElem!_pos,base1_post,Array.set_val_eq]
    exact Avx2.setOther _ _ _ _ (by decide)
  simp only [base2_post,base1_post,Array.set_val_eq,show (4#usize).val = 4 by rfl,
    show (5#usize).val = 5 by rfl,mi1_post,← getElem!_pos,mi4eq]
  interval_cases k <;> simp (disch := decide) only [prfWords,↓reduceIte,Avx2.setOther]
  all_goals first | rfl | (rw [Avx2.setSame _ _ _ (by simp)]; rfl)

private theorem read_set (xs : List Reg) (i k : Nat) (v : Reg) (hi : i < xs.length) (j : Fin 16) :
    (xs.set i v)[k]! j = if k = i then v j else xs[k]! j := by
  by_cases h : k = i
  · subst k; rw [Avx2.setSame _ _ _ hi]; simp
  · rw [Avx2.setOther _ _ _ _ (by omega)]; simp [h]

theorem leaf_message_spec (N : Usize) (base2 : Array Reg 16#usize) (high change : Reg)
    (prf : Array Reg 8#usize) (base : Fin 16 → Nat → Word) (idx : Reg)
    (hn : N.val = 16 ∨ N.val = 24 ∨ N.val = 32)
    (hh : ∀ j, high j = idx j <<< 16)
    (hb : ∀ k, k < 16 → ∀ j, base2.val[k]! j = prfWords (base j) (idx j) k) :
    leafMessage N base2 high (fun _ => 0xffff) change prf ⦃ r => ∀ k, k < 16 → ∀ j,
      r.val[k]! j = leafWords (base j) (fun i => prf.val[i]! j) (idx j) (change j) N.val k ⦄ := by
  unfold leafMessage
  simp only [_mm512_srli_epi32,_mm512_slli_epi32,_mm512_or_si512,_mm512_and_si512,_mm512_xor_si512,bind_ok]
  step as ⟨v2,h2⟩
  step as ⟨b3,h3⟩
  step as ⟨v0,h0⟩
  step as ⟨a,ha⟩
  step as ⟨q,hq⟩
  step with pack_words a prf q (by omega) (by omega) as ⟨w,hw⟩
  step*
  all_goals try scalar_tac
  intro k hk j
  have small : N.val/4 ≤ 8 ∧ 4 ≤ N.val/4 := by omega
  simp only [w1_post,Array.set_val_eq]
  rw [read_set _ _ _ _ (by scalar_tac) j]
  simp (disch := scalar_tac) only [mi12_post,mi14_post,h2,h0,← getElem!_pos,hw,ha,h3,Array.set_val_eq,
    read_set,show (2#usize).val = 2 by rfl,show (5#usize).val = 5 by rfl,
    hh,i9_post,i8_post,i7_post,hq,hb,leafWords,show (16#u32).bv.toNat%256 = 16 by rfl]
  by_cases k2 : k = 2
  · subst k; simp (disch := omega) only [prfWords,if_pos,if_neg]
  by_cases k5 : k = 5
  · subst k; simp (disch := omega) only [prfWords,if_pos,if_neg]
  by_cases last : k = 5+N.val/4
  · subst k; simp (disch := omega) only [prfWords,if_pos,if_neg]
  simp (disch := omega) only [if_neg]

end slhdsa.X86.Leaf
