module
public import Parent256.Types
@[expose] public section
open Aeneas Aeneas.Std
namespace TreeRust
abbrev sha256.x86.avx512.compress := DigestRust.sha256.x86.avx512.compress
abbrev sha256.x86.avx512.round := DigestRust.sha256.x86.avx512.round
abbrev sha256.x86.avx512.write_words {N : Usize} := @DigestRust.sha256.x86.avx512.write_words N
abbrev sha256.x86.avx512_available := DigestRust.sha256.x86.avx512_available

namespace core
abbrev slice.Slice.as_ptr {L : Usize} := @GatherRust.core.slice.Slice.as_ptr L
abbrev ptr.const_ptr.RawPtrConstT.cast {T : Type} := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast T
abbrev ptr.const_ptr.RawPtrConstT.add := GatherRust.core.ptr.const_ptr.RawPtrConstT.add
namespace core_arch.x86
abbrev avx512f._mm512_slli_epi32 := LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32
abbrev avx512f._mm512_or_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_or_si512
abbrev avx512f._mm512_set_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32
abbrev avx512f._mm512_broadcast_i32x4 := DigestRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4
abbrev avx512f._mm512_setzero_si512 := DigestRust.core.core_arch.x86.avx512f._mm512_setzero_si512
abbrev avx512f._mm512_mask_i32gather_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
abbrev avx512bw._mm512_shuffle_epi8 := DigestRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
end core_arch.x86
end core
end TreeRust
