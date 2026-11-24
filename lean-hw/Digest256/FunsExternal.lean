module
public import Digest256.Types
public import Store256.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace DigestRust

-- These are the extracted Rust functions checked in the Platform and Store256 packages.
abbrev sha256.x86.avx512.compress := PlatformRust.sha256.x86.avx512.compress
abbrev sha256.x86.avx512.round := PlatformRust.sha256.x86.avx512.round
abbrev sha256.x86.avx512.write_words {N : Usize} := @StoreRust.sha256.x86.avx512.write_words N
abbrev sha256.x86.avx512_available := GatherRust.sha256.x86.avx512_available
namespace core
abbrev slice.Slice.as_ptr {L : Usize} := @GatherRust.core.slice.Slice.as_ptr L
abbrev ptr.const_ptr.RawPtrConstT.cast {T : Type} := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast T
abbrev ptr.const_ptr.RawPtrConstT.add := GatherRust.core.ptr.const_ptr.RawPtrConstT.add
namespace core_arch.x86
open _root_.core.core_arch.x86
abbrev avx512bw._mm512_shuffle_epi8 := GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8
abbrev avx512f._mm512_broadcast_i32x4 := GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4
abbrev avx512f._mm512_setzero_si512 := GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512
def avx512f._mm512_mullo_epi32 (a b : __m512i) : Result __m512i := ok fun j => a j * b j
def avx512f._mm512_set_epi32 (p o n m l k j i h g f e d c b a : I32) : Result __m512i :=
  ok fun lane => [a.bv,b.bv,c.bv,d.bv,e.bv,f.bv,g.bv,h.bv,i.bv,j.bv,k.bv,l.bv,m.bv,n.bv,o.bv,p.bv][lane.val]!

def address (p : GatherRust.ReadPtr I32) (scale : I32) (v : __m512i) (j : Fin 16) : Int :=
  (p.offset : Int) + scale.bv.toInt * (v j).toInt
def little (a : List U8) (i : Nat) : BitVec 32 := a[i+3]!.bv ++ a[i+2]!.bv ++ a[i+1]!.bv ++ a[i]!.bv
/-- Each enabled lane must address four readable bytes in the source allocation. -/
def avx512f._mm512_mask_i32gather_epi32 (scale : I32) (src : __m512i) (mask : U16) (v : __m512i)
    (p : GatherRust.ReadPtr I32) : Result __m512i :=
  if scale.val ∈ ([1,2,4,8] : List Int) ∧ ∀ j : Fin 16, mask.bv.getLsbD j.val = true →
      0 ≤ address p scale v j ∧ address p scale v j + 4 ≤ (p.allocation.length : Int) then
    ok fun j => if mask.bv.getLsbD j.val then little p.allocation (address p scale v j).toNat else src j
  else fail .undef
end core_arch.x86
end core
end DigestRust
