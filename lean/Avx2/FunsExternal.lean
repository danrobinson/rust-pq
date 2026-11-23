module
public import Avx2.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace core.core_arch.x86
def __m256i.Insts.CoreCloneClone.clone (a : __m256i) : Result __m256i := ok a
def avx._mm256_setzero_si256 : Result __m256i := ok fun _ => 0
def avx._mm256_set_epi32 (a7 a6 a5 a4 a3 a2 a1 a0 : I32) : Result __m256i :=
  ok fun j => [a0.bv,a1.bv,a2.bv,a3.bv,a4.bv,a5.bv,a6.bv,a7.bv][j.val]!
def avx._mm256_set1_epi32 (x : I32) : Result __m256i := ok fun _ => x.bv
def avx2._mm256_add_epi32 (a b : __m256i) : Result __m256i := ok fun j => a j + b j
def avx2._mm256_and_si256 (a b : __m256i) : Result __m256i := ok fun j => a j &&& b j
def avx2._mm256_andnot_si256 (a b : __m256i) : Result __m256i := ok fun j => ~~~(a j) &&& b j
def avx2._mm256_or_si256 (a b : __m256i) : Result __m256i := ok fun j => a j ||| b j
def avx2._mm256_xor_si256 (a b : __m256i) : Result __m256i := ok fun j => a j ^^^ b j
def avx2._mm256_slli_epi32 (imm : I32) (a : __m256i) : Result __m256i := ok fun j => a j <<< (imm.bv.toNat % 256)
def avx2._mm256_srli_epi32 (imm : I32) (a : __m256i) : Result __m256i := ok fun j => a j >>> (imm.bv.toNat % 256)
end core.core_arch.x86
