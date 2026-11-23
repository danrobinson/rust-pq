import X86remainder.Funs
import Rcni.Top
import Rcavx.Top
import Streamscalar.Top
import Armstream.Proof
open Aeneas Aeneas.Std Result
open X86RemainderRust
namespace slhdsa.X86.Stream

theorem remainder256 (st : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :
    X86RemainderRust.sha256.stream.remainder st blocks ⦃ out =>
      slhdsa.wv out.val = fold256 (slhdsa.wv st.val) blocks.val ⦄ := by
  simp only [X86RemainderRust.sha256.stream.remainder,X86RemainderRust.sha256.stream.FORCE_SOFT,
    X86RemainderRust.sha256.stream.scalar_bmi2,sha2.sha256.compress256,
    RcDispatchRust.sha256.compress256,RcDispatchRust.sha256.compress,sha256.stream.hardware_backend.get,sha256.stream.has_bmi2.get,RcDispatchRust.sha256.shani_cpuid.get,bind_ok]
  generalize h0 : bmi2Available = bit0; cases bit0
  all_goals generalize h1 : RcDispatchRust.sha = bit1; cases bit1
  all_goals generalize h2 : RcDispatchRust.ssse3 = bit2; cases bit2
  all_goals generalize h3 : RcDispatchRust.sse41 = bit3; cases bit3
  all_goals simp only [Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true,Bool.false_eq_true,ite_false,ite_true,bind_ok]
  all_goals first | exact Intel.RustCrypto.compress_spec st blocks | exact scalar256 st blocks

theorem single256 (st : Array U32 8#usize) (data : Slice U8) (off : Usize) (room : off.val+64 ≤ data.length) :
    X86RemainderRust.sha256.compress st data off ⦃ out =>
      slhdsa.wv out.val = Spec.SHA256.compress (slhdsa.wv st.val) (((bytes data.val).drop off.val).take 64) ⦄ := by
  unfold X86RemainderRust.sha256.compress
  step as ⟨tail,ht,lt⟩
  step as ⟨part,hp,lp⟩
  have size : part.len = 64#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from,size,dite_eq_left trivial,
    core.result.Result.unwrap,X86RemainderRust.core.slice.raw.from_ref,ArmStreamRust.core.slice.raw.from_ref,bind_ok]
  apply WP.spec_mono (remainder256 st _)
  intro out eq
  simpa [fold256,hp,ht,bytes,List.slice,List.map_drop,List.map_take] using eq

theorem remainder512 (st : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :
    X86RemainderRust.sha512.stream.remainder st blocks ⦃ out =>
      slhdsa.S512.wv out.val = fold512 (slhdsa.S512.wv st.val) blocks.val ⦄ := by
  simp only [X86RemainderRust.sha512.stream.remainder,X86RemainderRust.sha512.stream.FORCE_SOFT,
    X86RemainderRust.sha512.stream.scalar_bmi2,sha2.sha512.compress512,
    RcDispatchRust.sha512.compress512,RcDispatchRust.sha512.compress,sha512.stream.hardware_backend.get,sha512.stream.has_bmi2.get,sha256.stream.has_bmi2.get,sha512.stream.dedicated.get,RcDispatchRust.sha512.avx2_cpuid.get,bind_ok]
  generalize h0 : bmi2Available = bit0; cases bit0
  all_goals generalize h1 : RcDispatchRust.sha = bit1; cases bit1
  all_goals generalize h2 : RcDispatchRust.avx2 = bit2; cases bit2
  all_goals simp only [Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true,Bool.false_eq_true,ite_false,ite_true,bind_ok]
  all_goals first | exact slhdsa.X86.RustCrypto512.compress_spec st blocks | exact scalar512 st blocks

theorem single512 (st : Array U64 8#usize) (data : Slice U8) (off : Usize) (room : off.val+128 ≤ data.length) :
    X86RemainderRust.sha512.compress st data off ⦃ out =>
      slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv st.val) (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold X86RemainderRust.sha512.compress
  step as ⟨tail,ht,lt⟩
  step as ⟨part,hp,lp⟩
  have size : part.len = 128#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from,size,dite_eq_left trivial,
    core.result.Result.unwrap,X86RemainderRust.core.slice.raw.from_ref,ArmStreamRust.core.slice.raw.from_ref,bind_ok]
  apply WP.spec_mono (remainder512 st _)
  intro out eq
  simpa [fold512,hp,ht,bytes,List.slice,List.map_drop,List.map_take] using eq

end slhdsa.X86.Stream
