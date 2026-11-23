import Streamscalar.Feed
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream
set_option maxRecDepth 8192

def rounds256 (t : Nat) (block : Spec.Bytes) (st : Array U32 8#usize) :=
  (List.range t).foldl (Spec.SHA256.round (Spec.SHA256.schedule block)) (state256 st)

theorem advance256 (I : Usize) (st v : Array U32 8#usize) (w : Array U32 16#usize) (block : Spec.Bytes)
    (bound : I.val < 64) (state : state256 v = rounds256 I.val block st)
    (old : window (slots256 w) (Spec.SHA256.schedule block) I.val) :
    StreamScalarRust.sha256.stream.scalar_step I v w ⦃ out next =>
      state256 out = rounds256 (I.val+1) block st ∧
      window (slots256 next) (Spec.SHA256.schedule block) (I.val+1) ⦄ := by
  apply WP.spec_mono (step256 I v w block bound old)
  rintro ⟨out,next⟩ ⟨round,ring⟩
  exact ⟨by simp only [round,state,rounds256,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil],ring⟩

theorem feed256_fips (st v : Array U32 8#usize) (block : Spec.Bytes)
    (rounds : state256 v = rounds256 64 block st) :
    StreamScalarRust.sha256.stream.scalar_loop0_loop0 ⟨0#usize,8#usize⟩ st v ⦃ out =>
      slhdsa.wv out.val = Spec.SHA256.compress (slhdsa.wv st.val) block ⦄ := by
  apply WP.spec_mono (feed256 st v)
  intro out added
  unfold Spec.SHA256.compress
  have idx (i : Nat) (hi : i < 8) : (slhdsa.wv st.val)[i]! = st.val[i]!.bv := by
    rw [slhdsa.wv_getElem! _ _ (by simpa using hi),getElem!_pos _ _ (by simpa using hi)]
  simp only [idx 0 (by decide),idx 1 (by decide),idx 2 (by decide),idx 3 (by decide),idx 4 (by decide),idx 5 (by decide),idx 6 (by decide),idx 7 (by decide)]
  unfold rounds256 state256 at rounds
  rw [← rounds]
  apply List.ext_getElem
  · simp [slhdsa.wv,state256]
  · intro i hi _
    have h : i < 8 := by simpa [slhdsa.wv] using hi
    have add := added i h
    rw [getElem!_pos out.val i (by simpa using h)] at add
    interval_cases i <;> simpa (disch := decide) [slhdsa.wv,state256,getElem!_pos] using add

def rounds512 (t : Nat) (block : Spec.Bytes) (st : Array U64 8#usize) :=
  (List.range t).foldl (Spec.SHA512.round (Spec.SHA512.schedule block)) (state512 st)

theorem advance512 (I : Usize) (st v : Array U64 8#usize) (w : Array U64 16#usize) (block : Spec.Bytes)
    (bound : I.val < 80) (state : state512 v = rounds512 I.val block st)
    (old : window (slots512 w) (Spec.SHA512.schedule block) I.val) :
    StreamScalarRust.sha512.stream.scalar_step I v w ⦃ out next =>
      state512 out = rounds512 (I.val+1) block st ∧
      window (slots512 next) (Spec.SHA512.schedule block) (I.val+1) ⦄ := by
  apply WP.spec_mono (step512 I v w block bound old)
  rintro ⟨out,next⟩ ⟨round,ring⟩
  exact ⟨by simp only [round,state,rounds512,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil],ring⟩

theorem feed512_fips (st v : Array U64 8#usize) (block : Spec.Bytes)
    (rounds : state512 v = rounds512 80 block st) :
    StreamScalarRust.sha512.stream.scalar_loop0_loop0 ⟨0#usize,8#usize⟩ st v ⦃ out =>
      slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv st.val) block ⦄ := by
  apply WP.spec_mono (feed512 st v)
  intro out added
  unfold Spec.SHA512.compress
  have idx (i : Nat) (hi : i < 8) : (slhdsa.S512.wv st.val)[i]! = st.val[i]!.bv := by
    rw [slhdsa.S512.wv_getElem! _ _ (by simpa using hi),getElem!_pos _ _ (by simpa using hi)]
  simp only [idx 0 (by decide),idx 1 (by decide),idx 2 (by decide),idx 3 (by decide),idx 4 (by decide),idx 5 (by decide),idx 6 (by decide),idx 7 (by decide)]
  unfold rounds512 state512 at rounds
  rw [← rounds]
  apply List.ext_getElem
  · simp [slhdsa.S512.wv,state512]
  · intro i hi _
    have h : i < 8 := by simpa [slhdsa.S512.wv] using hi
    have add := added i h
    rw [getElem!_pos out.val i (by simpa using h)] at add
    interval_cases i <;> simpa (disch := decide) [slhdsa.S512.wv,state512,getElem!_pos] using add

end slhdsa.X86.Stream
