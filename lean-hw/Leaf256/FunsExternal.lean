module
public import Leaf256.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace LeafRust
abbrev sha256.x86.avx512.compress := DigestRust.sha256.x86.avx512.compress
abbrev sha256.x86.avx512.round := DigestRust.sha256.x86.avx512.round
abbrev sha256.x86.avx512.write_words {N : Usize} := @DigestRust.sha256.x86.avx512.write_words N
abbrev sha256.x86.avx512_available := DigestRust.sha256.x86.avx512_available

namespace core.core_arch.x86.avx512f
open _root_.core.core_arch.x86
abbrev _mm512_set_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32
def _mm512_slli_epi32 (imm : U32) (v : __m512i) : Result __m512i := ok fun j => v j <<< (imm.bv.toNat % 256)
def _mm512_and_si512 (a b : __m512i) : Result __m512i := ok fun j => a j &&& b j
def _mm512_or_si512 (a b : __m512i) : Result __m512i := ok fun j => a j ||| b j
def _mm512_xor_si512 (a b : __m512i) : Result __m512i := ok fun j => a j ^^^ b j
end core.core_arch.x86.avx512f
end LeafRust
