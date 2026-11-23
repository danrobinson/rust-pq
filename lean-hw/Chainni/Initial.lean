import Chainni.Groups
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.Chain

def pack (state : Array U32 8#usize) := do
  let i ← Array.index_usize state 3#usize
  let i1 ← lift (UScalar.hcast .I32 i)
  let i2 ← Array.index_usize state 2#usize
  let i3 ← lift (UScalar.hcast .I32 i2)
  let i4 ← Array.index_usize state 1#usize
  let i5 ← lift (UScalar.hcast .I32 i4)
  let i6 ← Array.index_usize state 0#usize
  let i7 ← lift (UScalar.hcast .I32 i6)
  let abcd ← core.core_arch.x86.sse2._mm_set_epi32 i1 i3 i5 i7
  let i8 ← Array.index_usize state 7#usize
  let i9 ← lift (UScalar.hcast .I32 i8)
  let i10 ← Array.index_usize state 6#usize
  let i11 ← lift (UScalar.hcast .I32 i10)
  let i12 ← Array.index_usize state 5#usize
  let i13 ← lift (UScalar.hcast .I32 i12)
  let i14 ← Array.index_usize state 4#usize
  let i15 ← lift (UScalar.hcast .I32 i14)
  let efgh ← core.core_arch.x86.sse2._mm_set_epi32 i9 i11 i13 i15
  let cdab ← core.core_arch.x86.sse2._mm_shuffle_epi32 177#i32 abcd
  let hgfe ← core.core_arch.x86.sse2._mm_shuffle_epi32 27#i32 efgh
  let mi ← core.core_arch.x86.ssse3._mm_alignr_epi8 8#i32 cdab hgfe
  let mi1 ← ChainNiRust.core.core_arch.x86.sse41._mm_blend_epi16 240#i32 hgfe cdab
  ok (Array.make 2#usize [mi,mi1])

private theorem align8 (a b : Reg) :
    core.core_arch.x86.ssse3._mm_alignr_epi8 8#i32 a b = ok ⟨b.w2,b.w3,a.w0,a.w1⟩ := by
  cases a; cases b
  simp [core.core_arch.x86.ssse3._mm_alignr_epi8,get]

private theorem blend240 (a b : Reg) :
    ChainNiRust.core.core_arch.x86.sse41._mm_blend_epi16 240#i32 a b = ok ⟨a.w0,a.w1,b.w2,b.w3⟩ := by
  cases a; cases b
  simp [ChainNiRust.core.core_arch.x86.sse41._mm_blend_epi16,get]
  simp only [show 4294967295#32 = BitVec.allOnes 32 from rfl,BitVec.and_allOnes,and_self]

theorem pack_spec (state : Array U32 8#usize) :
    pack state ⦃ iv => stateWords (packedState iv) = wv state.val ⦄ := by
  unfold pack
  simp only [lift,bind_tc_eq,bind_ok,core.core_arch.x86.sse2._mm_set_epi32,
    core.core_arch.x86.sse2._mm_shuffle_epi32,align8,blend240]
  step*
  apply List.ext_getElem
  · simp [stateWords,wv]
  · intro k _ h
    have hk : k < 8 := by simpa [wv] using h
    interval_cases k <;> simp_all [packedState,decode,stateWords,wv,Array.make,get,UScalar.hcast_bv_eq]

end slhdsa.Intel.Chain
