import Chainwide.Funs
import Chainwrite.Walk
import Digest256.Block
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust.sha256.x86.avx512
open S512.Gather (flat flat_length)
abbrev sourcePtr (b : Rows) : GatherRust.ReadPtr U8 := ⟨flat b.val,0⟩

def inputWord (mask : U16) (b : Rows) (k : Nat) (j : Fin 16) : BitVec 32 :=
  if mask.bv.getLsbD j.val then Spec.SHA256.word (bytes b.val[j.val]!.val) (4*k) else 0

theorem read_word (N : Usize) (b : Rows) (m : U16) (v : Reg) (i : Usize)
    (hm : Covers m b.length) (hs : Digest.Stride v 64) (hn : 0 < b.length) (hi : i.val < 16) :
    chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N) (m,v,sourcePtr b,Store.control) i
    ⦃ r c => (∀ j, r j = inputWord m b i.val j) ∧ c = (m,v,sourcePtr b,Store.control) ⦄ := by
  unfold chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
  simp only [ChainWideRust.core.core_arch.x86.avx512f._mm512_setzero_si512,
    GatherRust.core.core_arch.x86.avx512f._mm512_setzero_si512,bind_ok]
  step as ⟨off,hoff⟩
  have hl : (flat b.val).length = b.length*64 := by rw [flat_length]; rfl
  have bound : off.val ≤ (flat b.val).length := by rw [hl]; omega
  simp only [ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add,sourcePtr,
    show ChainWideRust.MemoryElement.width U8 = 1 by rfl,Nat.mul_one,Nat.zero_add,bound,↓reduceIte,
    ChainWideRust.core.ptr.const_ptr.RawPtrConstT.cast,GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,bind_ok]
  apply WP.spec_bind (Digest.gather_spec b off.val m v (fun j h => hm _ h) hs (by change off.val+4 ≤ 64; omega))
  intro ws hw
  step with Store.shuffle ws as ⟨r,hr⟩
  refine ⟨?_,rfl⟩
  intro j
  rw [hr,hw]
  unfold Digest.active inputWord
  split <;> rename_i set
  · have bj := hm j.val set
    have safe : j.val*(64#usize).val + off.val + 4 ≤ (flat b.val).length := by change j.val*64+off.val+4 ≤ _; rw [hl]; omega
    rw [Digest.big_after_little _ _ safe,Digest.flat_word b.val _ _ bj (by change off.val+4 ≤ 64; omega)]
    simp [hoff,Nat.mul_comm]
  · rfl

theorem input_words (N : Usize) (b : Rows) (m : U16) (v : Reg)
    (hm : Covers m b.length) (hs : Digest.Stride v 64) (hn : 0 < b.length) :
    core.array.from_fn 16#usize (chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N)
      (m,v,sourcePtr b,Store.control) ⦃ words => ∀ k, k < 16 → ∀ j, words.val[k]! j = inputWord m b k j ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize
    (chains.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) _ (fun k w => ∀ j, w j = inputWord m b k j)
    (fun i hi => read_word N b m v i hm hs hn hi))
  intro a h k hk j
  simpa only [Array.getElem!_Nat_eq] using h k hk j

end slhdsa.X86.Chain
