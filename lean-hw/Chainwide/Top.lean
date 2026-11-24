import Chainwide.Driver
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust.sha256.x86.avx512

/-- Complete AVX-512 chain entry, including mixed or reversed intervals, untouched
bytes, all vector batches and the SHA-NI short-batch fallback when available. -/
theorem chains_spec (N : Usize) (state : Array U32 8#usize) (blocks : Rows) (starts ends : Slice U32)
    (hn : N.val=16 ∨ N.val=24 ∨ N.val=32) (hs : blocks.length ≤ starts.length) (he : blocks.length ≤ ends.length) :
    chains N state blocks starts ends ⦃ out => Intel.Chain.Ended N state blocks out starts ends ⦄ := by
  unfold chains
  conv => lhs; arg 1; equals (ok true) =>
    rcases hn with h|h|h <;> rw [h] <;> rfl
  simp only [bind_ok,massert,decide_true,ite_true]
  step with broadcast_spec N state as ⟨iv,initial⟩
  simp only [ChainWideRust.core.core_arch.x86.avx512f._mm512_set_epi32,DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32,
    core.core_arch.x86.sse2._mm_set_epi32,ChainWideRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,bind_ok]
  step as ⟨it,hi,hs16⟩
  apply driver_spec N state blocks starts ends iv _ it hn hs he _ (Leaf.initial_words iv state initial)
    (by simp [hi]) (by simp [hi]) hs16
  intro j
  fin_cases j <;> decide

#print axioms chains_spec
end slhdsa.X86.Chain
