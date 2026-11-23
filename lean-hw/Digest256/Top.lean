import Digest256.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Digest
open DigestRust.sha256.x86.avx512
open _root_.core.core_arch.x86

private theorem initial_spec (N L : Usize) (st : Array U32 8#usize) :
    core.array.Array.map (key_digests.closure.Insts.CoreOpsFunctionFnMutTupleU32__m512i N L) st ()
      ⦃ a => ∀ i, i < 8 → ∀ j : Fin 16, a.val[i]! j = st.val[i]!.bv ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize _ () (fun i v => ∀ j : Fin 16, v j = st.val[i]!.bv) ?_)
  · intro a h i hi j; simpa only [Array.getElem!_Nat_eq] using h i hi j
  intro i hi
  simp only [key_digests.closure.Insts.CoreOpsFunctionFnMutTupleU32__m512i,
    key_digests.closure.Insts.CoreOpsFunctionFnMutTupleU32__m512i.call_mut, lift, bind_ok,
    core.core_arch.x86.avx512f._mm512_set1_epi32]
  step*
  simp_all [step_simps, ← getElem!_pos]

private theorem initial_words (a : Array Reg 8#usize) (st : Array U32 8#usize)
    (ha : ∀ i, i < 8 → ∀ j : Fin 16, a.val[i]! j = st.val[i]!.bv) (j : Fin 16) :
    stateWords (laneState a j) = st.val.map (·.bv) := by
  simp (disch := decide) only [laneState, stateWords, ha]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi8 : i < 8 := by simpa using hj
    rw [List.getElem_map]
    interval_cases i <;> simp [getElem!_pos]


private def mkStride (s : Usize) : Reg := fun j =>
  ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : List (BitVec 32))[j.val]! * (show BitVec 32 from (UScalar.hcast .I32 s).bv)

private theorem mask_ok (n : Fin 17) (j : Fin 16) :
    ((65535#16) >>> (16-n.val)).getLsbD j.val = true ↔ j.val < n.val := by
  revert n j; decide +kernel

def expectedByte (seed : Array U32 8#usize) (data : Spec.Bytes) (k : Nat) :=
  ((hashed (seed.val.map (·.bv)) data 10)[k/4]!).extractLsb' (8*(3-k%4)) 8

private theorem groups_spec (N L : Usize) (seed : Array U32 8#usize) (rows : Slice (Array U8 L))
    (out : Slice (Array U8 N)) (hN : N.val = 16) (hL : L.val = 640)
    (hn : 0 < rows.length) (h16 : rows.length ≤ 16) (heq : out.length = rows.length) :
    key_digests seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 16, j.val < rows.length →
      ∀ k, k < N.val → (r.val[j.val]!.val[k]!).bv = expectedByte seed (bytes rows.val[j.val]!.val) k ⦄ := by
  unfold key_digests
  step with initial_spec N L seed as ⟨initial,hinit⟩
  step as ⟨shift,hshift⟩
  step as ⟨mask,hmask⟩
  simp only [DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32,bind_ok]
  step as ⟨stride,hstride⟩
  simp only [avx512f._mm512_set1_epi32,DigestRust.core.core_arch.x86.avx512f._mm512_mullo_epi32,
    sse2._mm_set_epi32,DigestRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,lift,bind_ok]
  have hm : Mask mask rows.length := by
    intro j
    unfold active
    have hb : mask.bv = core.num.U16.MAX.bv >>> shift.val := by assumption
    rw [hb,hshift]
    exact mask_ok ⟨rows.length,by omega⟩ j
  have hs : Stride (mkStride stride) L.val := by
    have hv : stride.val = 160 := by omega
    have hvb : (UScalar.hcast .I32 stride).bv = 160#32 := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.hcast_bv_eq,BitVec.toNat_setWidth]
      change stride.val % 2^32 = 160
      rw [hv]
    unfold Stride mkStride
    rw [hL,hvb]; intro j; fin_cases j <;> decide
  step as ⟨it,hit,hs0⟩
  have he : it = ⟨⟨0#usize,L⟩,64#usize⟩ := by cases it; simp_all
  rw [he]
  apply WP.spec_bind (hash_spec N L rows mask (mkStride stride) initial _ (initial_words initial seed hinit)
    hm hs hn (by omega))
  intro d hd
  apply WP.spec_mono (Store.write_words_spec d out (Or.inl hN) (by omega))
  rintro r ⟨hlen,hrow⟩
  refine ⟨hlen,fun j hj k hk => ?_⟩
  rw [hrow _ (by omega) _ hk]
  unfold Store.digestByte expectedByte
  have hidx : k/4 < 8 := by omega
  have hx : d.val[k/4]! j = (stateWords (laneState d j))[k/4]! := by
    generalize k/4 = i at *
    interval_cases i <;> rfl
  rw [hx,hd _ hj,hL]

theorem key_digests_spec (N L : Usize) (seed : Array U32 8#usize) (rows : Slice (Array U8 L))
    (out : Slice (Array U8 N)) (cpu : GatherRust.avx512Available = true)
    (hN : N.val = 16) (hL : L.val = 640)
    (hn : 0 < rows.length) (h16 : rows.length ≤ 16) (heq : out.length = rows.length) :
    DigestRust.sha256.x86.key_digests seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 16, j.val < rows.length →
      ∀ k, k < N.val → (r.val[j.val]!.val[k]!).bv = expectedByte seed (bytes rows.val[j.val]!.val) k ⦄ := by
  unfold DigestRust.sha256.x86.key_digests
  have equal : rows.len = out.len := by scalar_tac
  have size : rows.len ≤ 16#usize := h16
  have empty : core.slice.Slice.is_empty rows = ok false := by simp [core.slice.Slice.is_empty,hn.ne']
  have n : N = 16#usize := UScalar.eq_of_val_eq hN
  have l : L = 640#usize := UScalar.eq_of_val_eq hL
  simp only [DigestRust.sha256.x86.avx512_available,GatherRust.sha256.x86.avx512_available,cpu,
    massert,empty,← equal,size,n,l,decide_true,Bool.false_or,↓reduceIte,bind_ok,Bool.true_eq,Bool.false_eq_true,not_false_eq_true,eq_self]
  simpa only [n,l] using groups_spec N L seed rows out hN hL hn h16 heq

#print axioms key_digests_spec
end slhdsa.X86.Digest
