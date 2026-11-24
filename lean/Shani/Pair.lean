import Shani.Lane
import Avx2.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel
open ShaNiRust.sha256.x86 core.core_arch.x86

private theorem same_k : ShaNiRust.sha256.K.val.map (·.bv) = Spec.SHA256.K := by
  unfold ShaNiRust.sha256.K Spec.SHA256.K
  rfl

theorem pair_spec (t : Usize) (l r : ShaLane) (L R : List Word) (s : State) (ht : t.val < 16)
    (hl : Good l L s t.val) (hr : Good r R s t.val) (rl : Rec L) (rr : Rec R) :
    pair_group t l r ⦃ l' r' => Good l' L s (t.val+1) ∧ Good r' R s (t.val+1) ⦄ := by
  unfold pair_group
  simp only [sse2._mm_set_epi32, lift, bind_ok]
  step as ⟨idx, hidx⟩
  step as ⟨i1,hi1⟩
  step as ⟨k3,h3⟩
  step as ⟨i2,hi2⟩
  step as ⟨k2,h2⟩
  step as ⟨i3,hi3⟩
  step as ⟨k1,h1⟩
  step as ⟨k0,h0⟩
  have read (x : U32) (i : Usize) (bound : i.val < 64)
      (ev : x = ShaNiRust.sha256.K.val[i.val]'(by scalar_tac)) :
      I32.bv (UScalar.hcast .I32 x) = Spec.SHA256.K[i.val]! := by
    change x.bv = _
    rw [← same_k, getElem!_pos _ _ (by simp; scalar_tac), List.getElem_map, ev]
  have kg : (⟨I32.bv (UScalar.hcast .I32 k0),I32.bv (UScalar.hcast .I32 k1),
      I32.bv (UScalar.hcast .I32 k2),I32.bv (UScalar.hcast .I32 k3)⟩ : Reg) = group Spec.SHA256.K (4*t.val) := by
    simp only [read k0 idx (by scalar_tac) h0, read k1 i3 (by scalar_tac) h1,
      read k2 i2 (by scalar_tac) h2, read k3 i1 (by scalar_tac) h3, group, hi1,hi2,hi3,hidx]
  step with lane_spec t l _ L s ht hl kg rl
  step with lane_spec t r _ R s ht hr kg rr
  simp_all [step_simps]

@[step] theorem load_word (b : Array U8 64#usize) (i : Usize) (hi : i.val+4 ≤ 64) :
    load_group.word b i ⦃ x => x.bv = Spec.SHA256.word (bytes b.val) i.val ⦄ := by
  unfold load_group.word
  step*
  simp only [Spec.SHA256.word]
  repeat rw [bytes_getElem! _ _ (by scalar_tac)]
  subst_vars
  simp only [← getElem!_pos, i2_post, i4_post, i6_post]
  exact Avx2.be_four _ _ _ _

def blockGroup (B : Spec.Bytes) (n : Nat) : Reg := ⟨Spec.SHA256.word B n, Spec.SHA256.word B (n+4),
    Spec.SHA256.word B (n+8), Spec.SHA256.word B (n+12)⟩

@[step] theorem load_group_spec (b : Array U8 64#usize) (i : Usize) (hi : i.val+16 ≤ 64) :
    load_group b i ⦃ r => r = blockGroup (bytes b.val) i.val ⦄ := by
  unfold load_group
  simp only [sse2._mm_set_epi32]
  step*
  simp_all [blockGroup]

@[step] theorem load_spec (b : Array U8 64#usize) :
    compress_pair.closure.Insts.CoreOpsFunctionFnTupleShared0ArrayU864Array__m128i4.call () b ⦃ r =>
      r.val = [blockGroup (bytes b.val) 0,blockGroup (bytes b.val) 16,
        blockGroup (bytes b.val) 32,blockGroup (bytes b.val) 48] ⦄ := by
  unfold compress_pair.closure.Insts.CoreOpsFunctionFnTupleShared0ArrayU864Array__m128i4.call
  step*
#print axioms pair_spec
end slhdsa.Intel
