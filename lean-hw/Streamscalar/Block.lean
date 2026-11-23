import Streamscalar.Fips
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem block256 (st : Array U32 8#usize) (it next : core.slice.iter.Iter (Array U8 64#usize))
    (b : Array U8 64#usize) (more : core.slice.iter.IteratorSliceIter.next it = ok (some b,next)) :
    StreamScalarRust.sha256.stream.scalar_loop0.body it st ⦃ flow => ∃ out,
      flow = ControlFlow.cont (next,out) ∧
      slhdsa.wv out.val = Spec.SHA256.compress (slhdsa.wv st.val) (bytes b.val) ⦄ := by
  unfold StreamScalarRust.sha256.stream.scalar_loop0.body
  rw [more]
  simp only [bind_ok]
  apply WP.spec_bind (initial256 b)
  intro w hw
  have beginState : state256 st = rounds256 0 (bytes b.val) st := rfl
  iterate 64
    apply WP.spec_bind (advance256 _ st _ _ (bytes b.val) (by decide) (by assumption) (by assumption))
    rintro ⟨v,w⟩ ⟨hv,hw⟩
  apply WP.spec_bind (feed256_fips st _ (bytes b.val) (by assumption))
  intro out hash
  exact (WP.spec_ok _).mpr ⟨out,rfl,hash⟩

theorem block512 (st : Array U64 8#usize) (it next : core.slice.iter.Iter (Array U8 128#usize))
    (b : Array U8 128#usize) (more : core.slice.iter.IteratorSliceIter.next it = ok (some b,next)) :
    StreamScalarRust.sha512.stream.scalar_loop0.body it st ⦃ flow => ∃ out,
      flow = ControlFlow.cont (next,out) ∧
      slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv st.val) (bytes b.val) ⦄ := by
  unfold StreamScalarRust.sha512.stream.scalar_loop0.body
  rw [more]
  simp only [bind_ok]
  apply WP.spec_bind (initial512 b)
  intro w hw
  have beginState : state512 st = rounds512 0 (bytes b.val) st := rfl
  iterate 80
    apply WP.spec_bind (advance512 _ st _ _ (bytes b.val) (by decide) (by assumption) (by assumption))
    rintro ⟨v,w⟩ ⟨hv,hw⟩
  apply WP.spec_bind (feed512_fips st _ (bytes b.val) (by assumption))
  intro out hash
  exact (WP.spec_ok _).mpr ⟨out,rfl,hash⟩

end slhdsa.X86.Stream
