module
public import Platform.Types
@[expose] public section
open Aeneas Aeneas.Std Result

namespace slhdsa.X86

/-- At each bit, select the bit from hi when the mask is one and lo otherwise. -/
def selectWord {n} (mask hi lo : BitVec n) := (mask &&& hi) ||| (~~~mask &&& lo)

/-- VPTERNLOG uses the three source bits as bits 2, 1, 0 of the index into imm8. -/
def ternary {n} (imm : Nat) (a b c : BitVec n) : BitVec n :=
  let bit i : BitVec n := if imm.testBit i then ~~~0 else 0
  let pair i := selectWord c (bit (i+1)) (bit i)
  selectWord a (selectWord b (pair 6) (pair 4)) (selectWord b (pair 2) (pair 0))

end slhdsa.X86

namespace core.core_arch.x86.avx512f

def _mm512_add_epi32 (x y : __m512i) : Result __m512i := ok fun i => x i + y i

def _mm512_ternarylogic_epi32 (imm : I32) (a b c : __m512i) : Result __m512i :=
  ok fun i => slhdsa.X86.ternary (imm.bv.toNat % 256) (a i) (b i) (c i)

def _mm512_ror_epi32 (imm : I32) (a : __m512i) : Result __m512i :=
  ok fun i => (a i).rotateRight (imm.bv.toNat % 32)

def _mm512_set1_epi32 (a : I32) : Result __m512i := ok fun _ => a.bv

end core.core_arch.x86.avx512f
