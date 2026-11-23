module
public import Kdiag.Types
public import Kavx.FunsExternal
public import Parent512.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace KdiagRust
namespace core.core_arch.x86.avx512f
abbrev _mm512_ternarylogic_epi64 := KavxRust.core.core_arch.x86.avx512f._mm512_ternarylogic_epi64
abbrev _mm512_rol_epi64 := KavxRust.core.core_arch.x86.avx512f._mm512_rol_epi64
abbrev _mm512_xor_si512 := KavxRust.core.core_arch.x86.avx512f._mm512_xor_si512
abbrev _mm512_set1_epi64 := KavxRust.core.core_arch.x86.avx512f._mm512_set1_epi64
def _mm512_rolv_epi64 (a shifts : __m512i) : Result __m512i := ok fun i => (a i).rotateLeft ((shifts i).toNat % 64)
def _mm512_permutexvar_epi64 (idx a : __m512i) : Result __m512i := ok fun i => a ⟨(idx i).toNat % 8, Nat.mod_lt _ (by decide)⟩
def _mm512_mask_blend_epi64 (mask : U8) (a b : __m512i) : Result __m512i := ok fun i => if mask.bv.getLsbD i.val then b i else a i
def _mm512_mask_xor_epi64 (src : __m512i) (mask : U8) (a b : __m512i) : Result __m512i := ok fun i => if mask.bv.getLsbD i.val then a i ^^^ b i else src i
end core.core_arch.x86.avx512f
def core.intrinsics.transmute (_ : Type) (a : Array U64 8#usize) : Result core.core_arch.x86.__m512i :=
  ok fun i => a.val[i.val]!.bv
end KdiagRust
