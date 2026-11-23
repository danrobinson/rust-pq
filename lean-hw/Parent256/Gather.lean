import Parent256.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
open S512.Gather (flat flat_length)
open _root_.core.core_arch.x86
open DigestRust.core.core_arch.x86 (address little)

/-- One 32-bit word from each enabled pair of consecutive 16-byte children. -/
theorem gather_pairs (rows : Slice (Array U8 16#usize)) (start k count : Nat)
    (mask : U16) (stride : __m512i) (hm : Digest.Mask mask count)
    (hs : Digest.Stride stride 32) (hk : k < 8) (bound : 2*(start+count) ≤ rows.length) :
    TreeRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 4#i32 (fun _ => 0) mask stride
      ⟨flat rows.val,32*start+4*k⟩ ⦃ out => ∀ j,
        out j = if Digest.active mask j then little (flat rows.val) (32*(start+j.val)+4*k) else 0 ⦄ := by
  let p : GatherRust.ReadPtr I32 := ⟨flat rows.val,32*start+4*k⟩
  have ea (j : Fin 16) : address p 4#i32 stride j = (32*(start+j.val)+4*k : Nat) := by
    change ((32*start+4*k : Nat) : Int) + 4*(stride j).toInt = _
    rw [Int.mul_comm, hs j]
    push_cast
    omega
  have range (j : Fin 16) (h : mask.bv.getLsbD j.val = true) :
      0 ≤ address p 4#i32 stride j ∧ address p 4#i32 stride j + 4 ≤ (p.allocation.length : Int) := by
    have hj := (hm j).1 h
    rw [ea]
    change _ ∧ _ ≤ ((flat rows.val).length : Int)
    rw [flat_length]
    change 2*(start+count) ≤ rows.val.length at bound
    change _ ∧ _ ≤ ((rows.val.length * 16 : Nat) : Int)
    omega
  change DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32 _ _ _ _ p ⦃ _ => _ ⦄
  unfold DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
  rw [if_pos ⟨by decide,range⟩]
  simp only [step_simps]
  intro j
  rw [ea, Int.toNat_natCast]
  rfl

def childWord (rows : Slice (Array U8 16#usize)) (pair k : Nat) :=
  Spec.SHA256.word (bytes rows.val[2*pair+k/4]!.val) (4*(k%4))

theorem shuffled_pairs (rows : Slice (Array U8 16#usize)) (start k count : Nat)
    (mask : U16) (stride : __m512i) (hm : Digest.Mask mask count)
    (hs : Digest.Stride stride 32) (hk : k < 8) (bound : 2*(start+count) ≤ rows.length) :
    (do let w ← TreeRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
          4#i32 (fun _ => 0) mask stride ⟨flat rows.val,32*start+4*k⟩
        TreeRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8 w Store.control)
      ⦃ out => ∀ j, out j = if j.val < count then childWord rows (start+j.val) k else 0 ⦄ := by
  apply WP.spec_bind (gather_pairs rows start k count mask stride hm hs hk bound)
  intro w hw
  step with Store.shuffle w as ⟨r,hr⟩
  rename_i j
  rw [hr,hw]
  by_cases hj : j.val < count
  · rw [if_pos ((hm j).2 hj),if_pos hj]
    have hb : 32*(start+j.val)+4*k+4 ≤ (flat rows.val).length := by
      rw [flat_length]
      change 2*(start+count) ≤ rows.val.length at bound
      change _ ≤ rows.val.length * 16
      omega
    rw [Digest.big_after_little _ _ hb]
    unfold childWord
    have eq : 32*(start+j.val)+4*k =
        (2*(start+j.val)+k/4)*16+4*(k%4) := by omega
    rw [eq]
    apply Digest.flat_word
    · change 2*(start+count) ≤ rows.val.length at bound
      omega
    · change 4*(k%4)+4 ≤ 16
      omega
  · rw [if_neg (mt (hm j).1 hj),if_neg hj]
    rfl

end slhdsa.X86.Parent
