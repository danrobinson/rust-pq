import Chainwide.Batch
import Digest256.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust
open ChainWideRust.sha256.x86.avx512

def vectorBatch (N off : Usize) (b : Rows) (starts ends : Slice U32) (iv : Hash) (stride swap : Reg) : Result Rows := do
  let shift ← 16#usize - b.len
  let mask ← core.num.U16.MAX >>> shift
  let p ← core.slice.Slice.as_ptr b
  let ptr ← core.ptr.const_ptr.RawPtrConstT.cast U8 p
  let ranges ← loadRanges starts ends off mask
  let start := ranges.1
  let stop := ranges.2.1
  let active := ranges.2.2
  if active = 0#u16 then ok b else
    let zero ← core.core_arch.x86.avx512f._mm512_setzero_si512
    let saved := Array.repeat 8#usize zero
    let w ← core.array.from_fn 16#usize (chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N)
      (active,stride,ptr,swap)
    let word ← Array.index_usize w 4#usize
    let high ← lift (UScalar.hcast .I32 4294901760#u32)
    let bits ← core.core_arch.x86.avx512f._mm512_set1_epi32 high
    let fixed ← core.core_arch.x86.avx512f._mm512_and_si512 word bits
    let half ← core.core_arch.x86.avx512f._mm512_set1_epi32 65535#i32
    let pre ← chains_loop0_loop0 ⟨0#usize,4#usize⟩ w iv
    chains_loop0_loop1 N ends iv off b start stop active active saved w fixed half pre

def BatchAt (N off : Usize) (iv : Hash) (b out : Rows) (starts ends : Slice U32) :=
  out.length = b.length ∧ ∀ (j : Fin 16), j.val < b.length →
    bytes out.val[j.val]!.val = runBlock N.val (stateWords (laneState iv j)) (bytes b.val[j.val]!.val)
      starts.val[off.val+j.val]!.val ends.val[off.val+j.val]!.val

theorem vector_spec (N off : Usize) (b : Rows) (starts ends : Slice U32) (iv : Hash) (stride : Reg)
    (hn : N.val=16 ∨ N.val=24 ∨ N.val=32) (hb : 0 < b.length) (size : b.length ≤ 16)
    (hs : off.val+b.length ≤ starts.length) (he : off.val+b.length ≤ ends.length) (strideOK : Digest.Stride stride 64) :
    vectorBatch N off b starts ends iv stride Store.control ⦃ out => BatchAt N off iv b out starts ends ⦄ := by
  unfold vectorBatch
  step as ⟨shift,hshift⟩
  step as ⟨mask,hmask⟩
  have maskOK (j : Fin 16) : mask.bv.getLsbD j.val = true ↔ j.val < b.length := by
    have eq : mask.bv = core.num.U16.MAX.bv >>> shift.val := by assumption
    rw [eq,hshift]; exact Digest.mask_ok ⟨b.length,by omega⟩ j
  have base : core.slice.Slice.as_ptr b = ok (⟨S512.Gather.flat b.val,0⟩ : GatherRust.ReadPtr (Array U8 64#usize)) := rfl
  simp only [base,core.ptr.const_ptr.RawPtrConstT.cast,GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,bind_ok]
  step with load_ranges_spec starts ends off mask (by omega) (by omega) (fun j h => by have := (maskOK j).1 h; omega)
    as ⟨ranges,sched,st,en⟩
  rcases ranges with ⟨start,stop,active⟩
  simp only at sched st en ⊢
  have laneS (j : Fin 16) (hj : j.val < b.length) : start j = starts.val[off.val+j.val]!.bv := by
    rw [st,if_pos ((maskOK j).2 hj)]
  have laneE (j : Fin 16) (hj : j.val < b.length) : stop j = ends.val[off.val+j.val]!.bv := by
    rw [en,if_pos ((maskOK j).2 hj)]
  have covers : Covers active b.length := by
    intro k set
    have small : k < 16 := by by_contra! large; rw [BitVec.getLsbD_of_ge _ k large] at set; contradiction
    let j : Fin 16 := ⟨k,small⟩
    have live := sched.1 j
    rw [show active.bv.getLsbD j.val = true from set] at live
    by_contra! out
    have disabled : ¬mask.bv.getLsbD j.val = true := fun e => (Nat.not_lt.mpr out) ((maskOK j).1 e)
    have := of_decide_eq_true live.symm
    unfold Live at this
    rw [st,en,if_neg disabled,if_neg disabled] at this
    contradiction
  split <;> rename_i work
  · simp only [step_simps]
    refine ⟨rfl,?_⟩
    intro j hj
    have h := sched.1 j
    rw [work] at h
    have rev : ¬ Live start stop 0 j := by intro live; rw [decide_eq_true live] at h; simpa using h
    unfold Live at rev
    rw [laneS j hj,laneE j hj] at rev
    exact (runBlock_le _ _ _ _ _ (by simpa using rev)).symm
  · simp only [core.core_arch.x86.avx512f._mm512_setzero_si512,GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512,bind_ok]
    step with input_words N b active stride covers strideOK hb as ⟨w,hw⟩
    step as ⟨v,hv⟩
    simp only [lift,core.core_arch.x86.avx512f._mm512_set1_epi32,core.core_arch.x86.avx512f._mm512_and_si512,
      LeafRust.core.core_arch.x86.avx512f._mm512_and_si512,bind_ok]
    step with prefix_spec iv w (fun j => Leaf.blockOf (lanes w j))
      (fun k hk j => (Leaf.word_blockOf (lanes w j) k (by omega)).symm) as ⟨pre,hpre⟩
    apply WP.spec_mono (batch_loop_spec N ends iv off b start stop _ active _ pre w hn he covers work sched laneE hw
      (fun j => by rw [hv,← getElem!_pos]; rfl) hpre)
    rintro out ⟨len,rows⟩
    exact ⟨len,fun j hj => by simpa only [laneS j hj,laneE j hj,U32.bv_toNat] using rows j hj⟩

end slhdsa.X86.Chain
