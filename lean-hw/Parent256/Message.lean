import Parent256.Payload
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
open TreeRust.sha256.x86.avx512

def prepare (base : Array Reg 16#usize) (idx : Reg) (rows : Slice (Array U8 16#usize))
    (stride : Reg) (start : Usize) (mask : U16) := do
  let b4 ← Array.index_usize base 4#usize
  let indexHi ← _root_.core.core_arch.x86.avx512f._mm512_srli_epi32 16#u32 idx
  let w4 ← TreeRust.core.core_arch.x86.avx512f._mm512_or_si512 b4 indexHi
  let a ← Array.update base 4#usize w4
  let carry ← TreeRust.core.core_arch.x86.avx512f._mm512_slli_epi32 16#u32 idx
  let (w,last) ← fors_parents_loop1_loop0 ⟨0#usize,8#usize⟩ rows stride Store.control start mask a carry
  let b13 ← Array.index_usize w 13#usize
  let w13 ← TreeRust.core.core_arch.x86.avx512f._mm512_or_si512 last b13
  Array.update w 13#usize w13

theorem prepare_spec (base : Array Reg 16#usize) (idx : Reg) (rows : Slice (Array U8 16#usize))
    (stride : Reg) (start : Usize) (mask : U16) (count : Nat) (hm : Digest.Mask mask count)
    (hs : Digest.Stride stride 32) (hn : 0 < count) (bound : 2*(start.val+count) ≤ rows.length)
    (size : 32*(start.val+count) ≤ Usize.max) :
    prepare base idx rows stride start mask ⦃ w => ∀ k, k < 16 → ∀ j,
      w.val[k]! j = parentWords (fun i => base.val[i]! j) (fun i => sourceWord rows start.val count i j) (idx j) k ⦄ := by
  unfold prepare
  simp only [_root_.core.core_arch.x86.avx512f._mm512_srli_epi32,
    TreeRust.core.core_arch.x86.avx512f._mm512_or_si512,LeafRust.core.core_arch.x86.avx512f._mm512_or_si512,
    TreeRust.core.core_arch.x86.avx512f._mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,bind_tc_eq,bind_ok]
  step as ⟨b4,h4⟩
  step as ⟨a,ha⟩
  step with pack_children rows stride start mask count hm hs hn bound size a _ as ⟨pair,hw,hl⟩
  obtain ⟨w,last⟩ := pair
  simp only at hw hl
  step as ⟨b13,h13⟩
  step as ⟨out,ho⟩
  rename_i k hk j
  rw [ho,Array.set_val_eq,show (13#usize).val = 13 from rfl]
  have lookup (t : Nat) (ht : t < 16) : a.val[t]! j =
      if t=4 then base.val[4]! j ||| (idx j >>> 16) else base.val[t]! j := by
    rw [ha,Array.set_val_eq,show (4#usize).val = 4 from rfl]
    by_cases e : t=4
    · subst t
      rw [Avx2.setSame _ _ _ (by scalar_tac),if_pos rfl,h4,← getElem!_pos]
      rfl
    · rw [Avx2.setOther _ _ _ _ (Ne.symm e),if_neg e]
  by_cases e : k=13
  · subst k
    rw [Avx2.setSame _ _ _ (by scalar_tac),hl,h13,← getElem!_pos,hw 13 (by decide),lookup 13 (by decide)]
    rfl
  · rw [Avx2.setOther _ _ _ _ (Ne.symm e),hw k hk j]
    interval_cases k <;> simp_all (config := {failIfUnchanged := false}) only [parentWords,lookup,
      Nat.reduceLeDiff,Nat.reduceLT,Nat.reduceSub,↓reduceIte] <;> rfl

end slhdsa.X86.Parent
