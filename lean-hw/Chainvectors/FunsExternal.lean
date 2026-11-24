module
public import Chainvectors.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainVectorRust
namespace core.core_arch.x86
open _root_.core.core_arch.x86
namespace avx512f
abbrev _mm512_slli_epi32 := LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32
abbrev _mm512_and_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_and_si512
abbrev _mm512_or_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_or_si512
def _mm512_mask_mov_epi32 (src : __m512i) (mask : U16) (v : __m512i) : Result __m512i :=
  ok fun j => if mask.bv.getLsbD j.val then v j else src j
end avx512f
end core.core_arch.x86
end ChainVectorRust
