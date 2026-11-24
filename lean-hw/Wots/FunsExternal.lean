module
public import Wots.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace WotsRust
abbrev sha256.x86.avx512.compression_step := PlatformRust.sha256.x86.avx512.compression_step
abbrev sha256.x86.avx512.round := PlatformRust.sha256.x86.avx512.round
abbrev sha256.x86.avx512.write_words {N : Usize} := @StoreRust.sha256.x86.avx512.write_words N
def addressOf (a : address.Adrs) : slhdsa.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def hash.short_block (a : address.Adrs) := slhdsa.hash.short_block (addressOf a)

instance : ChainWideRust.MemoryElement I32 := ⟨4,fun x => x.bv.toLEBytes.map (fun b => ⟨b⟩)⟩
abbrev core.slice.Slice.as_ptr {T : Type} [ChainWideRust.MemoryElement T] := @ChainWideRust.core.slice.Slice.as_ptr T _
abbrev core.ptr.const_ptr.RawPtrConstT.add {T : Type} [ChainWideRust.MemoryElement T] := @ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add T _
abbrev core.ptr.const_ptr.RawPtrConstT.cast {T : Type} := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast T
abbrev core.num.U16.trailing_zeros := ChainWriteRust.core.num.U16.trailing_zeros

def core.slice.SliceArray.as_flattened {T : Type u} {N : Usize} (s : Slice (Array T N)) : Result (Slice T) :=
  let data := s.val.flatMap (·.val)
  if h : data.length ≤ Usize.max then ok (Slice.from data h) else fail .panic

namespace core.core_arch.x86
open _root_.core.core_arch.x86
abbrev __m512i.Insts.CoreCloneClone.clone := ChainWideRust.core.core_arch.x86.__m512i.Insts.CoreCloneClone.clone
abbrev avx512bw._mm512_shuffle_epi8 := GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
namespace avx512f
abbrev _mm512_slli_epi32 := LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32
abbrev _mm512_or_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_or_si512
abbrev _mm512_and_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_and_si512
abbrev _mm512_xor_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_xor_si512
abbrev _mm512_set_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32
abbrev _mm512_mullo_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_mullo_epi32
abbrev _mm512_mask_i32gather_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
abbrev _mm512_cmpeq_epi32_mask := ChainWideRust.core.core_arch.x86.avx512f._mm512_cmpeq_epi32_mask
abbrev _mm512_mask_mov_epi32 := ChainVectorRust.core.core_arch.x86.avx512f._mm512_mask_mov_epi32
abbrev _mm512_broadcast_i32x4 := GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4
abbrev _mm512_setzero_si512 := GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512
def _mm512_loadu_si512 (p : ConstRawPtr __m512i) : Result __m512i :=
  if p.offset+64 ≤ p.allocation.length then
    ok fun j => DigestRust.core.core_arch.x86.little p.allocation (p.offset+4*j.val)
  else fail .undef
def _mm512_cmpge_epi32_mask (a b : __m512i) : Result U16 :=
  ok (ChainWideRust.core.core_arch.x86.avx512f.laneMask fun lane => decide ((b lane).toInt ≤ (a lane).toInt))
def _mm512_mask_add_epi32 (src : __m512i) (mask : U16) (a b : __m512i) : Result __m512i :=
  ok fun j => if mask.bv.getLsbD j.val then a j + b j else src j
def _mm512_mask_sub_epi32 (src : __m512i) (mask : U16) (a b : __m512i) : Result __m512i :=
  ok fun j => if mask.bv.getLsbD j.val then a j - b j else src j
end avx512f
end core.core_arch.x86
end WotsRust
