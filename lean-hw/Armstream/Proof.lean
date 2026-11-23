import Armstream.Funs
import Slhdsa.Proofs.Hash
import Streamround.Blocks
open Aeneas Aeneas.Std Result
open ChainAvx2Rust (fullChunks remainder)
namespace slhdsa.PlatformStream
open X86.Stream

theorem bulk256 (st : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :
    ArmStreamRust.sha2.sha256.compress256 st blocks ⦃ out =>
      slhdsa.wv out.val = fold256 (slhdsa.wv st.val) blocks.val ⦄ := by
  unfold ArmStreamRust.sha2.sha256.compress256
  generalize blocks.val = bs
  induction bs generalizing st with
  | nil => exact (WP.spec_ok st).mpr rfl
  | cons b bs ih =>
    simp only [List.foldlM_cons,bind_tc_eq]
    apply WP.spec_bind (slhdsa.compress_portable_spec st b.to_slice 0#usize (by simp))
    intro next hash
    apply WP.spec_mono (ih next)
    intro out eq
    simpa only [fold256,List.foldl_cons,hash,Array.val_to_slice,show (0#usize).val=0 by rfl,List.drop_zero,
      List.take_of_length_le (show (bytes b.val).length ≤ 64 by simp)] using eq

/-- The extracted Arm stream driver, including the actual padding and digest functions,
matches the FIPS continued hash under the external compression contract. -/
theorem arm256_from (st : Array U32 8#usize) (pre : Usize) (msg : Slice U8)
    (aligned : pre.val%64=0) (space : Room (pre.val+msg.length) 72) :
    ArmStreamRust.sha256.sha256_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.ser (slhdsa.hashFrom (slhdsa.wv st.val) (slhdsa.padFrom pre.val (bytes msg.val))) ⦄ := by
  unfold ArmStreamRust.sha256.sha256_from
  simp only [ArmStreamRust.core.slice.Slice.as_chunks,show (64#usize).val ≠ 0 by decide,ite_false,bind_tc_eq,bind_ok]
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
  have padEq : ArmStreamRust.sha256.pad = slhdsa.sha256.pad := rfl
  have digestEq : ArmStreamRust.sha256.digest = slhdsa.sha256.digest := rfl
  rw [padEq,digestEq]
  step with bulk256 st _ as ⟨inter,hinter⟩
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
  step with bulk256 inter _ as ⟨final,hfinal⟩
  apply WP.spec_mono (slhdsa.digest_spec final)
  intro out serialized
  rw [serialized,hfinal,hinter,stream256_padding _ pre.val msg padded data]

theorem bulk512 (st : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :
    ArmStreamRust.sha2.sha512.compress512 st blocks ⦃ out =>
      slhdsa.S512.wv out.val = fold512 (slhdsa.S512.wv st.val) blocks.val ⦄ := by
  unfold ArmStreamRust.sha2.sha512.compress512
  generalize blocks.val = bs
  induction bs generalizing st with
  | nil => exact (WP.spec_ok st).mpr rfl
  | cons b bs ih =>
    simp only [List.foldlM_cons,bind_tc_eq]
    apply WP.spec_bind (slhdsa.S512.compress_portable_spec st b.to_slice 0#usize (by simp))
    intro next hash
    apply WP.spec_mono (ih next)
    intro out eq
    simpa only [fold512,List.foldl_cons,hash,Array.val_to_slice,show (0#usize).val=0 by rfl,List.drop_zero,
      List.take_of_length_le (show (bytes b.val).length ≤ 128 by simp)] using eq

/-- The extracted Arm stream driver, including the actual padding and digest functions,
matches the FIPS continued hash under the external compression contract. -/
theorem arm512_from (st : Array U64 8#usize) (pre : Usize) (msg : Slice U8)
    (space : pre.val+msg.length+144 ≤ Usize.max) :
    ArmStreamRust.sha512.sha512_from st pre msg ⦃ out =>
      bytes out.val = slhdsa.S512.ser (slhdsa.S512.hashFrom (slhdsa.S512.wv st.val) (slhdsa.S512.padFrom pre.val (bytes msg.val))) ⦄ := by
  unfold ArmStreamRust.sha512.sha512_from
  simp only [ArmStreamRust.core.slice.Slice.as_chunks,show (128#usize).val ≠ 0 by decide,ite_false,bind_tc_eq,bind_ok]
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
  have padEq : ArmStreamRust.sha512.pad = slhdsa.sha512.pad := rfl
  have digestEq : ArmStreamRust.sha512.digest = slhdsa.sha512.digest := rfl
  rw [padEq,digestEq]
  step with bulk512 st _ as ⟨inter,hinter⟩
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
  step with bulk512 inter _ as ⟨final,hfinal⟩
  apply WP.spec_mono (slhdsa.S512.digest_spec final)
  intro out serialized
  rw [serialized,hfinal,hinter,stream512_padding _ pre.val msg padded data]
theorem arm512_block (st : Array U64 8#usize) (data : Slice U8) (off : Usize)
    (room : off.val+128 ≤ data.length) :
    ArmStreamRust.sha512.compress st data off ⦃ out =>
      S512.wv out.val = Spec.SHA512.compress (S512.wv st.val) (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold ArmStreamRust.sha512.compress
  step as ⟨tail,ht,lt⟩
  all_goals try omega
  step as ⟨part,hp,lp⟩
  all_goals try omega
  have size : part.len = 128#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from,size,dif_pos trivial,
    core.result.Result.unwrap,ArmStreamRust.core.slice.raw.from_ref,bind_tc_eq,bind_ok]
  apply WP.spec_mono (bulk512 st _)
  intro out eq
  simpa [fold512,hp,ht,bytes,List.slice,List.map_drop,List.map_take] using eq

end slhdsa.PlatformStream
