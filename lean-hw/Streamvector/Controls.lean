import Streamvector.Gather
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

theorem offsets256 :
    DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32 240#i32 224#i32 208#i32 192#i32
      176#i32 160#i32 144#i32 128#i32 112#i32 96#i32 80#i32 64#i32 48#i32 32#i32 16#i32 0#i32
      ⦃ out => Digest.Stride out 64 ⦄ := by
  unfold DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32
  apply (WP.spec_ok _).mpr
  intro lane
  fin_cases lane <;> decide

theorem offsets512 :
    core.core_arch.x86.avx._mm256_set_epi32 112#i32 96#i32 80#i32 64#i32 48#i32 32#i32 16#i32 0#i32
      ⦃ out => S512.Gather.Stride out 128 ⦄ := by
  unfold core.core_arch.x86.avx._mm256_set_epi32
  apply (WP.spec_ok _).mpr
  intro lane
  fin_cases lane <;> decide

theorem swap256 :
    (do let small ← core.core_arch.x86.sse2._mm_set_epi32 0x0c0d0e0f#i32 0x08090a0b#i32 0x04050607#i32 0x00010203#i32
        GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4 small) = ok Store.control := by
  simp only [core.core_arch.x86.sse2._mm_set_epi32,bind_ok,GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4]
  congr 1

theorem swap512 :
    (do let small ← core.core_arch.x86.sse2._mm_set_epi32 0x08090a0b#i32 0x0c0d0e0f#i32 0x00010203#i32 0x04050607#i32
        GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4 small) = ok S512.Gather.swapControl := by
  simp only [core.core_arch.x86.sse2._mm_set_epi32,bind_ok,GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4]
  congr 1

end slhdsa.X86.Stream
