import Wots.Funs
import Leaf256.Prefix
import Leaf256.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512

theorem short_block_spec (a : WotsRust.address.Adrs) (m : Slice U8) (h : m.length ≤ 33) :
    WotsRust.hash.short_block a m ⦃ b => bytes b.val = padFrom 64 ((adrsS (WotsRust.addressOf a)).compress ++ bytes m.val) ⦄ :=
  slhdsa.short_block_spec (WotsRust.addressOf a) m h

theorem broadcast_spec (N L : Usize) (st : Array U32 8#usize) :
    core.array.Array.map (wots_endpoints.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i N L) st ()
      ⦃ a => ∀ i, i < 8 → ∀ lane : Fin 16, a.val[i]! lane = st.val[i]!.bv ⦄ :=
  Leaf.initial_spec N st

theorem read_word_spec (N L i : Usize) (b : Array U8 64#usize) (hi : i.val < 16) :
    wots_endpoints.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N) (L := L) b i
      ⦃ v b' => (∀ j : Fin 16, v j = Spec.SHA256.word (bytes b.val) (4*i.val)) ∧ b' = b ⦄ :=
  Leaf.read_word N b i hi

theorem words_spec (N L : Usize) (b : Array U8 64#usize) :
    core.array.from_fn 16#usize (wots_endpoints.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N L) b
      ⦃ w => ∀ k, k < 16 → ∀ j : Fin 16, w.val[k]! j = Spec.SHA256.word (bytes b.val) (4*k) ⦄ :=
  Leaf.words_spec N b

theorem first_two (iv : Array Reg 8#usize) (w : Array Reg 16#usize) (blocks : Fin 16 → Spec.Bytes)
    (hw : ∀ k, k < 2 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) :
    wots_endpoints_loop0 ⟨0#usize,2#usize⟩ w iv ⦃ s =>
      Trace s (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 2 ⦄ := by
  have body : wots_endpoints_loop0.body w = LeafRust.sha256.x86.avx512.fors_leaves_loop0.body w := by
    funext it s
    simp only [wots_endpoints_loop0.body,LeafRust.sha256.x86.avx512.fors_leaves_loop0.body,
      show WotsRust.sha256.K = LeafRust.sha256.K from by unfold WotsRust.sha256.K LeafRust.sha256.K; rfl]
    rfl
  unfold wots_endpoints_loop0
  simp_rw [body]
  exact Leaf.first_two iv w blocks hw

theorem recovery_words (N : Usize) (b : Array U8 64#usize) :
    core.array.from_fn 16#usize (recover.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) b
      ⦃ w => ∀ k, k < 16 → ∀ j : Fin 16, w.val[k]! j = Spec.SHA256.word (bytes b.val) (4*k) ⦄ :=
  Leaf.words_spec N b

end slhdsa.X86.Wots
