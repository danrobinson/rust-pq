module
public import Avx2.FunsExternal
public import Platform.FunsExternal
public import S8word.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace S8wordRust
open _root_.core.core_arch.x86
def core.core_arch.x86.avx512f._mm256_ternarylogic_epi32 (imm : I32) (a b c : __m256i) :
    Result __m256i := ok fun j => slhdsa.X86.ternary (imm.bv.toNat % 256) (a j) (b j) (c j)
def core.core_arch.x86.avx512f._mm256_ror_epi32 (imm : I32) (a : __m256i) :
    Result __m256i := ok fun j => (a j).rotateRight (imm.bv.toNat % 32)
def core.intrinsics.transmute (_Dst : Type) (v : __m256i) : Result (Array U32 8#usize) :=
  ok (Array.from (List.ofFn (fun j : Fin 8 => (⟨v j⟩ : U32))) (by simp))
end S8wordRust
