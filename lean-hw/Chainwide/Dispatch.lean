import Chainwide.Vector
import Chainni.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust.sha256.x86.avx512

def dispatch (N off : Usize) (state : Array U32 8#usize) (b : Rows) (starts ends : Slice U32)
    (iv : Hash) (stride swap : Reg) : Result Rows := do
  if b.len < 8#usize then
    let available ← ChainWideRust.sha256.x86.sha_ni.get
    if available then
      let ss ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U32) starts ⟨off⟩
      let es ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U32) ends ⟨off⟩
      ChainWideRust.sha256.x86.chains N state b ss es
    else vectorBatch N off b starts ends iv stride swap
  else vectorBatch N off b starts ends iv stride swap

theorem dispatch_spec (N off : Usize) (state : Array U32 8#usize) (b : Rows) (starts ends : Slice U32)
    (iv : Hash) (stride : Reg) (hn : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (hb : 0 < b.length) (size : b.length ≤ 16)
    (hs : off.val+b.length ≤ starts.length) (he : off.val+b.length ≤ ends.length) (strideOK : Digest.Stride stride 64)
    (init : ∀ j, stateWords (laneState iv j) = wv state.val) :
    dispatch N off state b starts ends iv stride Store.control ⦃ out =>
      out.length = b.length ∧ ∀ k < b.length, bytes out.val[k]!.val =
        runBlock N.val (wv state.val) (bytes b.val[k]!.val) starts.val[off.val+k]!.val ends.val[off.val+k]!.val ⦄ := by
  unfold dispatch
  have vector := vector_spec N off b starts ends iv stride hn hb size hs he strideOK
  split
  · simp only [ChainWideRust.sha256.x86.sha_ni.get,bind_ok]
    split
    · step as ⟨ss,hss,ls⟩
      step as ⟨es,hes,le⟩
      apply WP.spec_mono (Intel.Chain.chains_spec N state b ss es (by omega) (by omega) (by omega))
      rintro out ⟨len,rows⟩
      exact ⟨len,by simpa only [hss,hes,List.getElem!_drop] using rows⟩
    · apply WP.spec_mono vector
      rintro out ⟨len,rows⟩
      exact ⟨len,fun k hk => by simpa only [init] using rows ⟨k,by omega⟩ hk⟩
  · apply WP.spec_mono vector
    rintro out ⟨len,rows⟩
    exact ⟨len,fun k hk => by simpa only [init] using rows ⟨k,by omega⟩ hk⟩
end slhdsa.X86.Chain
