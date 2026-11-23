import Chainwide.Input
import Leaf256.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust.sha256.x86.avx512

theorem broadcast_spec (N : Usize) (st : Array U32 8#usize) :
    core.array.Array.map (chains.closure.Insts.CoreOpsFunctionFnMutTupleU32__m512i N) st ()
      ⦃ a => ∀ i, i < 8 → ∀ j : Fin 16, a.val[i]! j = st.val[i]!.bv ⦄ :=
  Leaf.initial_spec N st

theorem prefix_spec (iv : Array Reg 8#usize) (w : Array Reg 16#usize) (blocks : Fin 16 → Spec.Bytes)
    (hw : ∀ k, k < 4 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) :
    chains_loop0_loop0 ⟨0#usize,4#usize⟩ w iv ⦃ s =>
      Trace s (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 4 ⦄ := by
  have body : chains_loop0_loop0.body w = DigestRust.sha256.x86.avx512.key_digests_loop0_loop0.body w := by
    funext it s
    simp only [chains_loop0_loop0.body,DigestRust.sha256.x86.avx512.key_digests_loop0_loop0.body,
      show ChainWideRust.sha256.K = DigestRust.sha256.K from by unfold ChainWideRust.sha256.K DigestRust.sha256.K; rfl]
    rfl
  unfold chains_loop0_loop0
  simp_rw [body]
  exact Digest.first_four iv w blocks hw

theorem same_prefix (it : core.ops.range.Range Usize) (w : Array Reg 16#usize) (iv : Array Reg 8#usize) :
    chains_loop0_loop2 it w iv = chains_loop0_loop0 it w iv := rfl
end slhdsa.X86.Chain
