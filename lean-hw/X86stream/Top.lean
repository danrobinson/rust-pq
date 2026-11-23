import X86stream.Prefix
import Streamvector.Top
open Aeneas Aeneas.Std Result
open ChainAvx2Rust (fullChunks remainder)
namespace slhdsa.X86.Stream

theorem continued256 (st : Array U32 8#usize) (pre : Usize) (msg : Slice U8)
    (groups : usesVector256 (fullChunks 64#usize msg) → groupSpec256 st (fullChunks 64#usize msg))
    (aligned : pre.val%64=0) (space : Room (pre.val+msg.length) 72) :
    X86StreamRust.sha256.sha256_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.ser (slhdsa.hashFrom (slhdsa.wv st.val) (slhdsa.padFrom pre.val (bytes msg.val))) ⦄ := by
  unfold X86StreamRust.sha256.sha256_from
  simp only [X86StreamRust.core.slice.Slice.as_chunks,ArmStreamRust.core.slice.Slice.as_chunks,show (64#usize).val ≠ 0 by decide,ite_false,bind_tc_eq,bind_ok]
  have count := group_count (n := 64#usize) msg
  have tail := tail_size (n := 64#usize) msg
  change (fullChunks 64#usize msg).length = msg.length/64 at count
  change (remainder 64#usize msg).length = msg.length%64 at tail
  have limit : pre.val+msg.length ≤ Usize.max := by obtain ⟨cap,_⟩ := space; omega
  step as ⟨offset,hOff⟩
  all_goals try (change (fullChunks 64#usize msg).length * 64 ≤ _; omega)
  have offsetEq : offset.val = msg.length/64*64 := by rw [hOff]; change (fullChunks 64#usize msg).length * 64 = _; rw [count]
  step as ⟨pos,hPos⟩
  all_goals try omega
  have pad := slhdsa.pad_spec (remainder 64#usize msg) pos (by omega) (by obtain ⟨h₁,h₂⟩ := space; constructor <;> omega)
  have padEq : X86StreamRust.sha256.pad = slhdsa.sha256.pad := rfl
  have digestEq : X86StreamRust.sha256.digest = slhdsa.sha256.digest := rfl
  rw [padEq,digestEq]
  step with prefix256 st _ groups as ⟨tailBlocks,prefixState,hprefix⟩
  step with remainder256 prefixState tailBlocks as ⟨inter,hinter⟩
  step with pad as ⟨padding,hpad⟩
  let padded := alloc.vec.Vec.deref padding
  have data : bytes padded.val = slhdsa.padFrom (pre.val+msg.length/64*64) (bytes (remainder 64#usize msg).val) := by
    rw [← offsetEq,← hPos]; simpa only [padded,vec_deref_val] using hpad
  have multiple := slhdsa.padFrom_length (pre.val+msg.length/64*64) (bytes (remainder 64#usize msg).val)
  rw [← data] at multiple
  have empty : core.slice.Slice.is_empty (remainder 64#usize padded) = ok true := by
    have len := tail_size (n := 64#usize) padded
    have align : padded.length % (64#usize).val = 0 := by simpa [Slice.length] using multiple
    unfold core.slice.Slice.is_empty
    rw [len,align]; rfl
  rw [empty]
  simp only [bind_ok,massert,ite_true]
  step with remainder256 inter _ as ⟨final,hfinal⟩
  apply WP.spec_mono (slhdsa.digest_spec final)
  intro out serialized
  rw [serialized,hfinal,hinter,hprefix,stream256_padding _ pre.val msg padded data]

theorem continued512 (st : Array U64 8#usize) (pre : Usize) (msg : Slice U8)
    (groups : usesVector512 (fullChunks 128#usize msg) → groupSpec512 st (fullChunks 128#usize msg))
    (space : pre.val+msg.length+144 ≤ Usize.max) :
    X86StreamRust.sha512.sha512_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.S512.ser (slhdsa.S512.hashFrom (slhdsa.S512.wv st.val) (slhdsa.S512.padFrom pre.val (bytes msg.val))) ⦄ := by
  unfold X86StreamRust.sha512.sha512_from
  simp only [X86StreamRust.core.slice.Slice.as_chunks,ArmStreamRust.core.slice.Slice.as_chunks,show (128#usize).val ≠ 0 by decide,ite_false,bind_tc_eq,bind_ok]
  have count := group_count (n := 128#usize) msg
  have tail := tail_size (n := 128#usize) msg
  change (fullChunks 128#usize msg).length = msg.length/128 at count
  change (remainder 128#usize msg).length = msg.length%128 at tail
  have limit : pre.val+msg.length ≤ Usize.max := by omega
  step as ⟨offset,hOff⟩
  all_goals try (change (fullChunks 128#usize msg).length * 128 ≤ _; omega)
  have offsetEq : offset.val = msg.length/128*128 := by rw [hOff]; change (fullChunks 128#usize msg).length * 128 = _; rw [count]
  step as ⟨pos,hPos⟩
  all_goals try omega
  have pad := slhdsa.S512.pad_spec (remainder 128#usize msg) pos (by omega)
  have padEq : X86StreamRust.sha512.pad = slhdsa.sha512.pad := rfl
  have digestEq : X86StreamRust.sha512.digest = slhdsa.sha512.digest := rfl
  rw [padEq,digestEq]
  step with prefix512 st _ groups as ⟨tailBlocks,prefixState,hprefix⟩
  step with remainder512 prefixState tailBlocks as ⟨inter,hinter⟩
  step with pad as ⟨padding,hpad⟩
  let padded := alloc.vec.Vec.deref padding
  have data : bytes padded.val = slhdsa.S512.padFrom (pre.val+msg.length/128*128) (bytes (remainder 128#usize msg).val) := by
    rw [← offsetEq,← hPos]; simpa only [padded,vec_deref_val] using hpad
  have multiple := slhdsa.S512.padFrom_length (pre.val+msg.length/128*128) (bytes (remainder 128#usize msg).val)
  rw [← data] at multiple
  have empty : core.slice.Slice.is_empty (remainder 128#usize padded) = ok true := by
    have len := tail_size (n := 128#usize) padded
    have align : padded.length % (128#usize).val = 0 := by simpa [Slice.length] using multiple
    unfold core.slice.Slice.is_empty
    rw [len,align]; rfl
  rw [empty]
  simp only [bind_ok,massert,ite_true]
  step with remainder512 inter _ as ⟨final,hfinal⟩
  apply WP.spec_mono (slhdsa.S512.digest_spec final)
  intro out serialized
  rw [serialized,hfinal,hinter,hprefix,stream512_padding _ pre.val msg padded data]


theorem short256 (st : Array U32 8#usize) (pre : Usize) (msg : Slice U8)
    (short : msg.length < 1024)
    (aligned : pre.val%64=0) (space : Room (pre.val+msg.length) 72) :
    X86StreamRust.sha256.sha256_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.ser (slhdsa.hashFrom (slhdsa.wv st.val) (slhdsa.padFrom pre.val (bytes msg.val))) ⦄ := by
  apply continued256 st pre msg _ aligned space
  intro selected
  have required := selected.1
  rw [group_count] at required
  change 16 ≤ msg.length/64 at required
  omega

theorem short512 (st : Array U64 8#usize) (pre : Usize) (msg : Slice U8)
    (short : msg.length < 1024)
    (space : pre.val+msg.length+144 ≤ Usize.max) :
    X86StreamRust.sha512.sha512_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.S512.ser (slhdsa.S512.hashFrom (slhdsa.S512.wv st.val) (slhdsa.S512.padFrom pre.val (bytes msg.val))) ⦄ := by
  apply continued512 st pre msg _ space
  intro selected
  have required := selected.1
  rw [group_count] at required
  change 8 ≤ msg.length/128 at required
  omega


theorem fallback256 (st : Array U32 8#usize) (pre : Usize) (msg : Slice U8)
    (fallback : X86StreamRust.vectorAvailable = false ∨ RcDispatchRust.sha = true)
    (aligned : pre.val%64=0) (space : Room (pre.val+msg.length) 72) :
    X86StreamRust.sha256.sha256_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.ser (slhdsa.hashFrom (slhdsa.wv st.val) (slhdsa.padFrom pre.val (bytes msg.val))) ⦄ := by
  apply continued256 st pre msg _ aligned space
  intro selected
  rcases selected with ⟨_,vector,dedicated⟩
  rcases fallback with noVector | shaNi <;> simp_all

theorem fallback512 (st : Array U64 8#usize) (pre : Usize) (msg : Slice U8)
    (fallback : X86StreamRust.vectorAvailable = false)
    (space : pre.val+msg.length+144 ≤ Usize.max) :
    X86StreamRust.sha512.sha512_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.S512.ser (slhdsa.S512.hashFrom (slhdsa.S512.wv st.val) (slhdsa.S512.padFrom pre.val (bytes msg.val))) ⦄ := by
  apply continued512 st pre msg _ space
  intro selected
  obtain ⟨_,vector⟩ := selected
  simp_all

theorem stream256 (st : Array U32 8#usize) (pre : Usize) (msg : Slice U8)
    (aligned : pre.val%64=0) (space : Room (pre.val+msg.length) 72) :
    X86StreamRust.sha256.sha256_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.ser (slhdsa.hashFrom (slhdsa.wv st.val) (slhdsa.padFrom pre.val (bytes msg.val))) ⦄ :=
  continued256 st pre msg (fun _ => prescheduled256 st _) aligned space

theorem stream512 (st : Array U64 8#usize) (pre : Usize) (msg : Slice U8)
    (space : pre.val+msg.length+144 ≤ Usize.max) :
    X86StreamRust.sha512.sha512_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.S512.ser (slhdsa.S512.hashFrom (slhdsa.S512.wv st.val) (slhdsa.S512.padFrom pre.val (bytes msg.val))) ⦄ :=
  continued512 st pre msg (fun _ => prescheduled512 st _) space

end slhdsa.X86.Stream
