module
public import S8table.Types
public import S8word.Funs
public import Digest256.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace S8tableRust
abbrev sha256.stream.expand := S8wordRust.sha256.stream.expand
namespace core
abbrev slice.Slice.as_ptr {L : Usize} := @GatherRust.core.slice.Slice.as_ptr L
abbrev ptr.const_ptr.RawPtrConstT.cast {T : Type} := @GatherRust.core.ptr.const_ptr.RawPtrConstT.cast T
abbrev ptr.const_ptr.RawPtrConstT.add := GatherRust.core.ptr.const_ptr.RawPtrConstT.add
namespace core_arch.x86
open _root_.core.core_arch.x86
def avx2._mm256_broadcastsi128_si256 (x : __m128i) : Result __m256i :=
  ok fun j => slhdsa.Intel.get x j.val
def byteAt (x : __m256i) (i : Nat) : BitVec 8 :=
  (x ⟨i/4%8, Nat.mod_lt _ (by decide)⟩).extractLsb' (8*(i%4)) 8
def avx2._mm256_shuffle_epi8 (x control : __m256i) : Result __m256i :=
  let byte (i : Nat) :=
    let sel := byteAt control i
    if sel.getLsbD 7 then 0#8 else byteAt x (16*(i/16)+sel.toNat%16)
  ok fun j => byte (4*j.val+3) ++ byte (4*j.val+2) ++ byte (4*j.val+1) ++ byte (4*j.val)
def address (p : GatherRust.ReadPtr I32) (scale : I32) (v : __m256i) (j : Fin 8) : Int :=
  (p.offset : Int) + scale.bv.toInt * (v j).toInt
def avx2._mm256_i32gather_epi32 (scale : I32) (p : GatherRust.ReadPtr I32) (v : __m256i) : Result __m256i :=
  if scale.val ∈ ([1,2,4,8] : List Int) ∧ ∀ j, 0 ≤ address p scale v j ∧
      address p scale v j + 4 ≤ (p.allocation.length : Int) then
    ok fun j => DigestRust.core.core_arch.x86.little p.allocation (address p scale v j).toNat
  else fail .undef
end core_arch.x86
end core
end S8tableRust
