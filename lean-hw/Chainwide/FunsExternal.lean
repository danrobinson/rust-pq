module
public import Chainwide.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace ChainWideRust
abbrev sha256.x86.avx512.compression_step := PlatformRust.sha256.x86.avx512.compression_step
abbrev sha256.x86.avx512.round := PlatformRust.sha256.x86.avx512.round
abbrev sha256.x86.avx512.write_finished := ChainWriteRust.sha256.x86.avx512.write_finished
abbrev sha256.x86.avx512.chain_address := ChainVectorRust.sha256.x86.avx512.chain_address
abbrev sha256.x86.avx512.chain_value := ChainVectorRust.sha256.x86.avx512.chain_value
abbrev sha256.x86.avx512.chain_done := ChainVectorRust.sha256.x86.avx512.chain_done
abbrev sha256.x86.chains := ChainNiRust.sha256.x86.chains

opaque shaNiAvailable : Bool
def sha256.x86.sha_ni.get : Result Bool := ok shaNiAvailable

class MemoryElement (T : Type) where
  width : Nat
  encode : T → List U8

instance : MemoryElement U8 := ⟨1,fun x => [x]⟩
instance : MemoryElement U32 := ⟨4,fun x => x.bv.toLEBytes.map (fun b => ⟨b⟩)⟩
instance {n : Usize} : MemoryElement (Array U8 n) := ⟨n.val,fun x => x.val⟩

def core.slice.Slice.as_ptr {T : Type} [MemoryElement T] (s : Slice T) : Result (ConstRawPtr T) :=
  ok ⟨s.val.flatMap MemoryElement.encode,0⟩
abbrev core.ptr.const_ptr.RawPtrConstT.cast {T : Type} := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast T
def core.ptr.const_ptr.RawPtrConstT.add {T : Type} [MemoryElement T] (p : ConstRawPtr T) (i : Usize) :
    Result (ConstRawPtr T) :=
  let off := p.offset + i.val * MemoryElement.width T
  if off ≤ p.allocation.length then ok ⟨p.allocation,off⟩ else fail .undef

namespace core.core_arch.x86
open _root_.core.core_arch.x86
namespace avx512f
abbrev _mm512_set_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32
abbrev _mm512_mask_i32gather_epi32 := DigestRust.core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
abbrev _mm512_and_si512 := LeafRust.core.core_arch.x86.avx512f._mm512_and_si512
abbrev _mm512_setzero_si512 := GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512
abbrev _mm512_broadcast_i32x4 := GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4

def laneMask (f : Fin 16 → Bool) : U16 := ⟨(BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)⟩
def _mm512_cmplt_epu32_mask (x y : __m512i) : Result U16 := ok (laneMask fun j => decide ((x j).toNat < (y j).toNat))
def _mm512_cmpeq_epi32_mask (x y : __m512i) : Result U16 := ok (laneMask fun j => x j == y j)
def _mm512_maskz_loadu_epi32 (mask : U16) (p : ConstRawPtr I32) : Result __m512i :=
  if ∀ j : Fin 16, mask.bv.getLsbD j.val = true → p.offset+4*j.val+4 ≤ p.allocation.length then
    ok fun j => if mask.bv.getLsbD j.val then DigestRust.core.core_arch.x86.little p.allocation (p.offset+4*j.val) else 0
  else fail .undef
end avx512f
abbrev avx512bw._mm512_shuffle_epi8 := GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
def __m512i.Insts.CoreCloneClone.clone (x : __m512i) : Result __m512i := ok x
end core.core_arch.x86
end ChainWideRust
