import Chainavx2.Reassemble
open Aeneas Aeneas.Std Result
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust
open ChainAvx2Rust.sha256.x86.avx2

theorem initial_words (iv : EightRegs) (state : Array U32 8#usize)
    (broadcast : ∀ i, i < 8 → ∀ j : Fin 8, iv.val[i]! j = state.val[i]!.bv) (j : Fin 8) :
    X86.stateWords (laneState iv j) = wv state.val := by
  simp (disch := decide) only [X86.stateWords,laneState,broadcast]
  apply List.ext_getElem
  · simp [wv]
  · intro i hi hj
    have h8 : i < 8 := by simpa [wv] using hj
    simp only [wv,List.getElem_map]
    interval_cases i <;> simp [getElem!_pos]

/-- Byte-for-byte refinement of every complete AVX2 group and the portable tail,
including partial digest words and reversed unsigned counter ranges. -/
theorem chains_spec (N : Usize) (state : Array U32 8#usize) (blocks : Intel.Chain.Rows)
    (starts ends : Slice U32) (hn : N.val ≤ 32) (hs : blocks.length ≤ starts.length)
    (he : blocks.length ≤ ends.length) :
    chains N state blocks starts ends ⦃ out => Intel.Chain.Ended N state blocks out starts ends ⦄ := by
  unfold chains
  step with broadcast_spec N state as ⟨iv,init⟩
  simp only [ChainAvx2Rust.core.slice.Slice.as_chunks_mut,show (8#usize).val ≠ 0 by decide,ite_false,bind_ok]
  have gs := group_size blocks
  have fit : 8*(blocks.length/8) ≤ blocks.length := by omega
  have ub := blocks.property
  step as ⟨off,hoff⟩
  have pos : off.val = 8*(blocks.length/8) := by rw [hoff]; change 8*(fullChunks 8#usize blocks).length = _; rw [gs]
  step with groups_spec N iv starts ends (fullChunks 8#usize blocks) hn (by omega) (by omega) as ⟨g,hg⟩
  step as ⟨ss,hss,ls⟩
  step as ⟨es,hes,le⟩
  have tailVal : (remainder 8#usize blocks).val = blocks.val.drop off.val := by
    simp only [remainder,Slice.from_val,pos]; rfl
  have tailLen : (remainder 8#usize blocks).length = blocks.length-off.val := by
    change (remainder 8#usize blocks).val.length = _; rw [tailVal,List.length_drop]
  step with chain_blocks_portable_spec N hn state (remainder 8#usize blocks) ss es (by omega) (by omega) as ⟨tail,tl,rows⟩
  apply reassemble N state iv blocks tail g starts ends (initial_words iv state init) (gs ▸ hg) (by omega)
  intro k hk
  simpa only [tailVal,hss,hes,List.getElem!_drop,pos] using rows k (by omega)
end slhdsa.Avx2.Chain
