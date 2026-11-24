module
public import Platform.Types
@[expose] public section
open Aeneas Aeneas.Std Result

namespace slhdsa.X86

/-- At each bit, select the bit from hi when the mask is one and lo otherwise. -/
def selectWord {n} (mask hi lo : BitVec n) := (mask &&& hi) ||| (~~~mask &&& lo)

/-- VPTERNLOG uses the three source bits as bits 2, 1, 0 of the index into imm8. -/
def ternary {n} (imm : Nat) (a b c : BitVec n) : BitVec n :=
  let bit i : BitVec n := if imm.testBit i then BitVec.allOnes n else 0#n
  let pair i := selectWord c (bit (i+1)) (bit i)
  selectWord a (selectWord b (pair 6) (pair 4)) (selectWord b (pair 2) (pair 0))

/-- Quadwords pair consecutive low and high doublewords, with the low word first. -/
def word64 (v : core.core_arch.x86.__m512i) (i : Fin 8) : BitVec 64 :=
  v ⟨2*i.val+1, by omega⟩ ++ v ⟨2*i.val, by omega⟩

def ofWords64 (f : Fin 8 → BitVec 64) (i : Fin 16) : BitVec 32 :=
  (f ⟨i.val/2, by omega⟩).extractLsb' (32*(i.val%2)) 32

@[simp] theorem word64_ofWords64 (f : Fin 8 → BitVec 64) (i : Fin 8) :
    word64 (ofWords64 f) i = f i := by
  unfold word64 ofWords64
  simp [Nat.mul_add_div, Nat.add_mod]
  exact BitVec.extractLsb'_append_extractLsb' (x := f i) (w := 32) (len := 32)

end slhdsa.X86

namespace core.core_arch.x86.avx512f

def _mm512_add_epi32 (x y : __m512i) : Result __m512i := ok fun i => x i + y i

def _mm512_ternarylogic_epi32 (imm : I32) (a b c : __m512i) : Result __m512i :=
  ok fun i => slhdsa.X86.ternary (imm.bv.toNat % 256) (a i) (b i) (c i)

def _mm512_ror_epi32 (imm : I32) (a : __m512i) : Result __m512i :=
  ok fun i => (a i).rotateRight (imm.bv.toNat % 32)

def _mm512_set1_epi32 (a : I32) : Result __m512i := ok fun _ => a.bv

open slhdsa.X86

def _mm512_srli_epi32 (imm : U32) (a : __m512i) : Result __m512i :=
  ok fun i => a i >>> (imm.bv.toNat % 256)

def _mm512_add_epi64 (a b : __m512i) : Result __m512i :=
  ok (ofWords64 fun i => word64 a i + word64 b i)

def _mm512_ternarylogic_epi64 (imm : I32) (a b c : __m512i) : Result __m512i :=
  ok (ofWords64 fun i => ternary (imm.bv.toNat % 256) (word64 a i) (word64 b i) (word64 c i))

def _mm512_ror_epi64 (imm : I32) (a : __m512i) : Result __m512i :=
  ok (ofWords64 fun i => (word64 a i).rotateRight (imm.bv.toNat % 64))

def _mm512_srli_epi64 (imm : U32) (a : __m512i) : Result __m512i :=
  ok (ofWords64 fun i => word64 a i >>> (imm.bv.toNat % 256))

def _mm512_set1_epi64 (a : I64) : Result __m512i := ok (ofWords64 fun _ => a.bv)

end core.core_arch.x86.avx512f
