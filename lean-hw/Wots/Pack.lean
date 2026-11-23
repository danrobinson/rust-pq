import Wots.Funs
import Chainvectors.Words
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open WotsRust.core.core_arch.x86.avx512f
open _root_.core.core_arch.x86.avx512f

abbrev Words := Array Reg 16#usize
abbrev Hash := Array Reg 8#usize

/-- Insert the high counter halfword for each SIMD lane. -/
def packHigh (N : Usize) (w : Words) (hash : Hash) (mi half : Reg) : Result Words := do
  let mi1 ← Array.index_usize hash 0#usize
  let mi2 ← _mm512_srli_epi32 16#u32 mi1
  let mi3 ← _mm512_or_si512 mi mi2
  let a ← Array.update w 5#usize mi3
  let i1 ← N / 4#usize
  let w1 ← wots_endpoints_loop1_loop0_loop0 ⟨1#usize,i1⟩ a hash
  let i2 ← i1 - 1#usize
  let mi4 ← Array.index_usize hash i2
  let mi5 ← _mm512_slli_epi32 16#u32 mi4
  let i3 ← 5#usize + i1
  let mi6 ← Array.index_usize w1 i3
  let mi7 ← _mm512_and_si512 mi6 half
  let mi8 ← _mm512_or_si512 mi5 mi7
  let i4 ← 5#usize + i1
  Array.update w1 i4 mi8

/-- The first digest word shares a message word with the WOTS step counter. -/
def pack (N : Usize) (w : Words) (hash : Hash) (t : I32) (half : Reg) : Result Words := do
  let i ← t <<< 16#i32
  let mi ← _mm512_set1_epi32 i
  packHigh N w hash mi half

def packedWord (old hash : Nat → BitVec 32) (n : Nat) (t : BitVec 32) (k : Nat) :=
  if k = 5 then (t <<< 16) ||| (hash 0 >>> 16) else Chain.valueWord old hash n k

theorem pack_high_spec (N : Usize) (w : Words) (hash : Hash) (counter : Reg)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) :
    packHigh N w hash (fun j => counter j <<< 16) (fun _ => 0xffff) ⦃ out => ∀ k, k < 16 → ∀ j,
      out.val[k]! j = packedWord (fun i => w.val[i]! j) (fun i => hash.val[i]! j) N.val (counter j) k ⦄ := by
  unfold packHigh
  simp only [_mm512_set1_epi32,_mm512_srli_epi32,_mm512_slli_epi32,_mm512_and_si512,_mm512_or_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_and_si512,
    LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,bind_ok]
  step as ⟨first,hf⟩
  step as ⟨a,ha⟩
  step as ⟨lim,hl⟩
  have bounds : 1 ≤ lim.val ∧ lim.val ≤ 8 := by omega
  rw [show wots_endpoints_loop1_loop0_loop0 = ChainVectorRust.sha256.x86.avx512.chain_value_loop by rfl]
  step with Chain.interior_spec a hash lim (by omega) (by omega) as ⟨middle,hm⟩
  step as ⟨last,hn⟩
  step as ⟨h,hh⟩
  step as ⟨pos,hpos⟩
  step as ⟨wlast,hwl⟩
  step as ⟨pos',hp'⟩
  step as ⟨out,ho⟩
  rename_i k hk j
  have av (i : Nat) (hi : i < 16) : a.val[i]! j =
      if i=5 then (counter j <<< 16) ||| (hash.val[0]! j >>> 16) else w.val[i]! j := by
    rw [ha,Array.set_val_eq,show (5#usize).val = 5 by rfl]
    by_cases e : i=5
    · subst i; rw [Avx2.setSame _ _ _ (by simp),if_pos rfl,hf,← getElem!_pos]; simp_all
    · rw [Avx2.setOther _ _ _ _ (Ne.symm e),if_neg e]
  have wl : wlast j = w.val[pos.val]! j := by
    rw [hwl,← getElem!_pos,hm _ (by omega),if_neg (by omega),av _ (by omega),if_neg (by omega)]
  rw [ho,Array.set_val_eq]
  by_cases e : k=pos'.val
  · subst k
    rw [Avx2.setSame _ _ _ (by scalar_tac),wl,hh,← getElem!_pos]
    simp (disch := omega) only [packedWord,Chain.valueWord,if_neg (show pos'.val ≠ 5 by omega),if_pos (show pos'.val = 5+N.val/4 by omega)]
    rw [show last.val = N.val/4-1 by omega,show pos.val=pos'.val by omega]; rfl
  · rw [Avx2.setOther _ _ _ _ (Ne.symm e),hm k hk j]
    by_cases mid : 6 ≤ k ∧ k < 5+lim.val
    · rw [if_pos mid]
      simp only [packedWord,Chain.valueWord,if_neg (show k ≠ 5 by omega),if_neg (show k ≠ 5+N.val/4 by omega),if_pos (show 6 ≤ k ∧ k < 5+N.val/4 by omega)]
    · rw [if_neg mid,av k hk]
      by_cases key : k=5
      · simp only [packedWord,key,ite_true]
      · simp (disch := omega) only [packedWord,Chain.valueWord,if_neg key,if_neg (show k ≠ 5+N.val/4 by omega),if_neg (show ¬(6 ≤ k ∧ k < 5+N.val/4) by omega)]
theorem pack_spec (N : Usize) (w : Words) (hash : Hash) (t : I32)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) :
    pack N w hash t (fun _ => 0xffff) ⦃ out => ∀ k, k < 16 → ∀ j,
      out.val[k]! j = packedWord (fun i => w.val[i]! j) (fun i => hash.val[i]! j) N.val t.bv k ⦄ := by
  unfold pack
  step as ⟨shift,hs⟩
  simp only [_mm512_set1_epi32,bind_ok]
  have bits : shift.bv = t.bv <<< 16 := by simp_all
  rw [bits]
  exact pack_high_spec N w hash (fun _ => t.bv) shape

end slhdsa.X86.Wots
