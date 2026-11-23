import Rcavx.Funs
import Rcavx.Array
import Spec.Sha512
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def sigma0Trace (x : BitVec 64) :=
  ((x >>> 7) ^^^ (x >>> 1) ^^^ (x <<< 56) ^^^ ((x >>> 1) >>> 7) ^^^ ((x <<< 56) <<< 7))
def sigma1Trace (x : BitVec 64) :=
  ((x >>> 6) ^^^ (x <<< 3) ^^^ (x >>> 19) ^^^ ((x <<< 3) <<< 42) ^^^ ((x >>> 19) >>> 42))

private theorem xorCycle (a b c : Bool) : (a != (b != c)) = (b ^^ (c ^^ a)) := by
  cases a <;> cases b <;> cases c <;> decide

theorem sigma0Trace_eq (x : BitVec 64) : sigma0Trace x = Spec.SHA512.ssig0 x := by
  unfold sigma0Trace Spec.SHA512.ssig0
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_rotateRight, BitVec.getLsbD_of_ge,
      Bool.xor_comm, Bool.xor_assoc, Bool.xor_left_comm] <;> first | apply xorCycle | symm; apply xorCycle | apply Bool.xor_comm | rfl
theorem sigma1Trace_eq (x : BitVec 64) : sigma1Trace x = Spec.SHA512.ssig1 x := by
  unfold sigma1Trace Spec.SHA512.ssig1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_rotateRight, BitVec.getLsbD_of_ge,
      Bool.xor_comm, Bool.xor_assoc, Bool.xor_left_comm] <;> first | apply xorCycle | symm; apply xorCycle | apply Bool.xor_comm | rfl

theorem align8 (a b : Lane) : align 8#i32 a b = (b.2,a.1) := by
  rcases a with ⟨al,ah⟩; rcases b with ⟨bl,bh⟩
  change (((ah ++ al ++ (bh ++ bl)).extractLsb' 64 64),((ah ++ al ++ (bh ++ bl)).extractLsb' 128 64)) = _
  congr 1 <;> bv_decide

def generated (a b e f h : Lane) : Lane :=
  let base := zip (· + ·) a (align 8#i32 f e)
  let plus0 := zip (· + ·) base (map sigma0Trace (align 8#i32 b a))
  zip (· + ·) plus0 (map sigma1Trace h)

theorem update (a b c d e f g h k : Lane) :
    sha512.x86_avx2.sha512_update_x_avx (Array.make 8#usize [a,b,c,d,e,f,g,h]) k =
    let nw := generated a b e f h
    ok (zip (· + ·) nw k,Array.make 8#usize [b,c,d,e,f,g,h,nw]) := by
  simp only [sha512.x86_avx2.sha512_update_x_avx,core.core_arch.x86.sse2._mm_srli_epi64,core.core_arch.x86.sse2._mm_slli_epi64,core.core_arch.x86.sse2._mm_add_epi64,core.core_arch.x86.sse2._mm_xor_si128,core.core_arch.x86.ssse3._mm_alignr_epi8,bind_ok,at0,put0,at1,put1,at2,put2,at3,put3,at4,put4,at5,put5,at6,put6,at7,put7]
  rfl

theorem update2 (a b c d e f g h k : Wide) :
    sha512.x86_avx2.sha512_update_x_avx2 (Array.make 8#usize [a,b,c,d,e,f,g,h]) k =
    let nw := (generated a.1 b.1 e.1 f.1 h.1,generated a.2 b.2 e.2 f.2 h.2)
    ok ((zip (· + ·) nw.1 k.1,zip (· + ·) nw.2 k.2),Array.make 8#usize [b,c,d,e,f,g,h,nw]) := by
  simp only [sha512.x86_avx2.sha512_update_x_avx2,core.core_arch.x86.avx2._mm256_srli_epi64,core.core_arch.x86.avx2._mm256_slli_epi64,core.core_arch.x86.avx2._mm256_add_epi64,core.core_arch.x86.avx2._mm256_xor_si256,core.core_arch.x86.avx2._mm256_alignr_epi8,bind_ok,at0,put0,at1,put1,at2,put2,at3,put3,at4,put4,at5,put5,at6,put6,at7,put7]
  rfl

theorem generated_fips (a b e f h : Lane) :
    generated a b e f h =
    (a.1+e.2+Spec.SHA512.ssig0 a.2+Spec.SHA512.ssig1 h.1,
     a.2+f.1+Spec.SHA512.ssig0 b.1+Spec.SHA512.ssig1 h.2) := by
  simp [generated,align8,zip,map,sigma0Trace_eq,sigma1Trace_eq]

end slhdsa.X86.RustCrypto512
