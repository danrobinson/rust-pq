import Digest256.Read
import Gather512.Read
import Streamround.Read
open Aeneas Aeneas.Std Result
open core.core_arch.x86
namespace slhdsa.X86.Stream
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
open S512.Gather (flat flat_length)

/-- The full-mask gather reads the selected four bytes of each consecutive
64-byte block. The 128-bit-lane shuffle restores big-endian SHA word order. -/
theorem gathered256 (blocks : Array (Array U8 64#usize) 16#usize) (v : __m512i)
    (stride : Digest.Stride v 64) (k : Nat) (hk : k < 16) :
    (do let x ← DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
          4#i32 (fun _ => 0) 65535#u16 v ⟨flat blocks.val,4*k⟩
        GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8 x Store.control)
      ⦃ out => ∀ j : Fin 16, out j = (Spec.SHA256.schedule (bytes blocks.val[j.val]!.val))[k]! ⦄ := by
  have bound (j : Fin 16) : j.val < blocks.to_slice.length := by simpa [Slice.length] using j.isLt
  have pos : 4*k+4 ≤ (64#usize).val := by change 4*k+4 ≤ 64; omega
  have gather := Digest.gather_spec blocks.to_slice (4*k) 65535#u16 v (fun j _ => bound j) stride pos
  simp only [Array.val_to_slice] at gather
  step with gather as ⟨x,hx⟩
  step with Store.shuffle x as ⟨out,hout⟩
  rename_i j
  have active : Digest.active 65535#u16 j = true := by fin_cases j <;> decide
  have endpos : j.val*64+4*k+4 ≤ (flat blocks.val).length := by
    rw [flat_length]; simp; omega
  rw [hout,hx j,if_pos active,Digest.big_after_little _ _ endpos,
    slhdsa.schedule_lt16 _ _ hk]
  exact Digest.flat_word blocks.val j.val _ (by simpa using j.isLt) pos

theorem gathered512 (blocks : Array (Array U8 128#usize) 8#usize) (v : __m256i)
    (stride : S512.Gather.Stride v 128) (k : Nat) (hk : k < 16) :
    (do let x ← GatherRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi64
          8#i32 (fun _ => 0) 255#u8 v ⟨flat blocks.val,8*k⟩
        GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8 x S512.Gather.swapControl)
      ⦃ out => ∀ j : Fin 8, word64 out j = (Spec.SHA512.schedule (bytes blocks.val[j.val]!.val))[k]! ⦄ := by
  have mask : S512.Gather.Mask 255#u8 blocks.to_slice.length := by
    intro j
    fin_cases j <;> simp [S512.Gather.active,Slice.length] <;> decide
  have pos : 8*k+8 ≤ (128#usize).val := by change 8*k+8 ≤ 128; omega
  have gather := S512.Gather.gather_spec blocks.to_slice (8*k) 255#u8 v mask stride pos
  simp only [Array.val_to_slice] at gather
  step with gather as ⟨x,ws,hx,hw⟩
  subst x
  step with S512.Gather.shuffle_swap (ofWords64 ws) as ⟨out,hout⟩
  rename_i j
  have active : S512.Gather.active 255#u8 j = true := by fin_cases j <;> decide
  have endpos : j.val*128+8*k+8 ≤ (flat blocks.val).length := by
    rw [flat_length]; simp; omega
  rw [hout,S512.Gather.ofWords_even,S512.Gather.ofWords_odd,hw j,if_pos active,S512.Gather.big_after_little _ _ endpos,
    slhdsa.H512.schedule_lt16 _ _ hk]
  exact S512.Gather.flat_word blocks.val j.val _ (by simpa using j.isLt) pos

end slhdsa.X86.Stream
