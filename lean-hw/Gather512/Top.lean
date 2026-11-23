import Gather512.Hash
import Gather512.Write
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather
open GatherRust.sha512.x86
open _root_.core.core_arch.x86

private theorem broadcast_spec (N L : Usize) (seed : Array U64 8#usize) :
    core.array.Array.map (digest_groups.closure.Insts.CoreOpsFunctionFnMutTupleU64__m512i N L) seed () ⦃ a =>
      ∀ j, stateWords (laneState a j) = seed.val.map (·.bv) ⦄ := by
  apply WP.spec_mono (Parents.initial_spec N seed)
  exact fun a ha j => Parents.initial_words a seed ha j

private def mkStride (s : Usize) : __m256i := fun j =>
  ([0,1,2,3,4,5,6,7] : List (BitVec 32))[j.val]! * (show BitVec 32 from (UScalar.hcast .I32 s).bv)

private theorem mask_ok (n : Fin 9) (j : Fin 8) :
    ((255#8) >>> (8-n.val)).getLsbD j.val = true ↔ j.val < n.val := by
  revert n j; decide

/-- Multi-block SHA-512 over already-padded WOTS public-key inputs. All active output
rows contain the requested leading bytes of the independent compression chain. -/
theorem groups_spec (N L : Usize) (seed : Array U64 8#usize) (rows : Slice (Array U8 L)) (out : Slice (Array U8 N))
    (shape : (N.val = 24 ∧ L.val = 1280) ∨ (N.val = 32 ∧ L.val = 2304))
    (hn : 0 < rows.length) (h8 : rows.length ≤ 8) (heq : out.length = rows.length) :
    digest_groups seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 8, j.val < rows.length →
      r.val[j.val]!.val = Parents.encoded ((hashed (seed.val.map (·.bv)) (bytes rows.val[j.val]!.val) (L.val/128)).take (N.val/8)) ⦄ := by
  unfold digest_groups
  step as ⟨shift,hshift⟩
  step as ⟨mask,hmask⟩
  step with broadcast_spec N L seed as ⟨initial,hinit⟩
  simp only [avx._mm256_set_epi32, avx._mm256_set1_epi32, GatherRust.core.core_arch.x86.avx2._mm256_mullo_epi32,
    sse2._mm_set_epi32, GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4, lift, bind_ok]
  step as ⟨stride,hstride⟩
  have hm : Mask mask rows.length := by
    intro j
    unfold active
    have hb : mask.bv = core.num.U8.MAX.bv >>> shift.val := by assumption
    rw [hb,hshift]
    exact mask_ok ⟨rows.length,by omega⟩ j
  have hs : Stride (mkStride stride) L.val := by
    rcases shape with ⟨_,h⟩ | ⟨_,h⟩
    · have hv : stride.val = 160 := by omega
      have hvb : (UScalar.hcast .I32 stride).bv = 160#32 := by
        apply BitVec.eq_of_toNat_eq
        simp only [UScalar.hcast_bv_eq,BitVec.toNat_setWidth]
        change stride.val % 2^32 = 160
        rw [hv]
      unfold Stride mkStride
      rw [h,hvb]; intro j; fin_cases j <;> decide
    · have hv : stride.val = 288 := by omega
      have hvb : (UScalar.hcast .I32 stride).bv = 288#32 := by
        apply BitVec.eq_of_toNat_eq
        simp only [UScalar.hcast_bv_eq,BitVec.toNat_setWidth]
        change stride.val % 2^32 = 288
        rw [hv]
      unfold Stride mkStride
      rw [h,hvb]; intro j; fin_cases j <;> decide
  simp (disch := decide) only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default, ↓reduceIte, bind_ok]
  have it_ok : (128#usize).val ≠ 0 := by decide
  simp only [it_ok,↓reduceIte,bind_ok]
  apply WP.spec_bind (hash_spec N L rows mask (mkStride stride) initial _ hinit hm hs hn (by omega))
  intro d hd
  step as ⟨last,hl⟩
  apply WP.spec_mono (write_spec N out d last hl (by omega) (by omega))
  rintro r ⟨hrows,hw⟩
  refine ⟨hrows, fun j hj => ?_⟩
  rw [hw j (by omega),hd j hj]

#print axioms groups_spec

/-- The checked Rust entry point including CPU dispatch and every shape assertion. -/
theorem key_digests_spec (N L : Usize) (seed : Array U64 8#usize) (rows : Slice (Array U8 L)) (out : Slice (Array U8 N))
    (cpu : GatherRust.avx512Available = true)
    (shape : (N.val = 24 ∧ L.val = 1280) ∨ (N.val = 32 ∧ L.val = 2304))
    (hn : 0 < rows.length) (h8 : rows.length ≤ 8) (heq : out.length = rows.length) :
    key_digests seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 8, j.val < rows.length →
      r.val[j.val]!.val = Parents.encoded ((hashed (seed.val.map (·.bv)) (bytes rows.val[j.val]!.val) (L.val/128)).take (N.val/8)) ⦄ := by
  unfold key_digests
  simp only [GatherRust.sha256.x86.avx512_available,cpu,bind_ok]
  have equal : rows.len = out.len := by scalar_tac
  have size : rows.len ≤ 8#usize := h8
  have empty : core.slice.Slice.is_empty rows = ok false := by simp [core.slice.Slice.is_empty,hn.ne']
  have hok := groups_spec N L seed rows out shape hn h8 heq
  rcases shape with ⟨a,b⟩ | ⟨a,b⟩ <;>
    simp only [a,b,massert, empty, ← equal, size, decide_true, decide_false,
      ↓reduceIte,bind_ok, Bool.true_eq, Bool.false_eq_true, not_false_eq_true, eq_self] <;>
    simpa only [a,b] using hok

#print axioms key_digests_spec
end slhdsa.X86.S512.Gather
