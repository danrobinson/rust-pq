module
public import Gather512.Types
@[expose] public section
open Aeneas Aeneas.Std Result
open slhdsa.X86
namespace GatherRust
/-- A read pointer tracks its offset into the bytes of one live source allocation. -/
structure ReadPtr (_ : Type) where
  allocation : List U8
  offset : Nat

def core.slice.Slice.as_ptr {n : Usize} (s : Slice (Array U8 n)) : Result (ReadPtr (Array U8 n)) :=
  ok ⟨s.val.flatMap (·.val), 0⟩

def core.ptr.const_ptr.RawPtrConstT.cast {T : Type} (U : Type) (p : ReadPtr T) : Result (ReadPtr U) :=
  ok ⟨p.allocation,p.offset⟩

/-- The extracted pointer arithmetic adds bytes after casting the data pointer to u8. -/
def core.ptr.const_ptr.RawPtrConstT.add (p : ReadPtr U8) (i : Usize) : Result (ReadPtr U8) :=
  if p.offset + i.val ≤ p.allocation.length then ok ⟨p.allocation,p.offset+i.val⟩ else fail .undef

namespace core.core_arch.x86
open _root_.core.core_arch.x86
def avx2._mm256_mullo_epi32 (x y : __m256i) : Result __m256i := ok fun j => x j * y j
def avx512f._mm512_setzero_si512 : Result __m512i := ok fun _ => 0
def avx512f._mm512_broadcast_i32x4 (x : __m128i) : Result __m512i :=
  ok fun j => slhdsa.Intel.get x j.val
def byteAt (x : __m512i) (idx : Nat) : BitVec 8 :=
  (x ⟨idx / 4 % 16, Nat.mod_lt _ (by decide)⟩).extractLsb' (8*(idx%4)) 8
def avx512bw._mm512_shuffle_epi8 (x control : __m512i) : Result __m512i :=
  let byte (i : Nat) :=
    let sel := byteAt control i
    if sel.getLsbD 7 then 0#8 else byteAt x (16*(i/16)+sel.toNat%16)
  ok fun j => byte (4*j.val+3) ++ byte (4*j.val+2) ++ byte (4*j.val+1) ++ byte (4*j.val)

def address (p : ReadPtr I64) (scale : I32) (v : __m256i) (j : Fin 8) : Int :=
  (p.offset : Int) + scale.bv.toInt * (v j).toInt
def littleWord (a : List U8) (i : Nat) : BitVec 64 :=
  a[i+7]!.bv ++ a[i+6]!.bv ++ a[i+5]!.bv ++ a[i+4]!.bv ++ a[i+3]!.bv ++ a[i+2]!.bv ++ a[i+1]!.bv ++ a[i]!.bv
/-- Masked-off lanes do not read memory. Enabled lanes require eight readable bytes
at the signed, scaled effective offset into the allocation. -/
def avx512f._mm512_mask_i32gather_epi64 (scale : I32) (src : __m512i) (mask : U8) (v : __m256i) (p : ReadPtr I64) :
    Result __m512i :=
  if scale.val ∈ ([1,2,4,8] : List Int) ∧ ∀ j : Fin 8, mask.bv.getLsbD j.val = true →
      0 ≤ address p scale v j ∧ address p scale v j + 8 ≤ (p.allocation.length : Int) then
    ok (ofWords64 fun j => if mask.bv.getLsbD j.val then littleWord p.allocation (address p scale v j).toNat else word64 src j)
  else fail .undef
end core.core_arch.x86
end GatherRust

/-- CPU/OS feature availability supplied by the runtime detector. -/
opaque GatherRust.avx512Available : Bool
def GatherRust.sha256.x86.avx512_available : Result Bool := ok GatherRust.avx512Available
