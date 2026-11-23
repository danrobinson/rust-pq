import X86remainder.Funs
import Streamscalar.Top
import Armstream.Proof
open Aeneas Aeneas.Std Result
open X86RemainderRust
namespace slhdsa.X86.Stream

theorem remainder256 (st : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :
    X86RemainderRust.sha256.stream.remainder st blocks ⦃ out =>
      slhdsa.wv out.val = fold256 (slhdsa.wv st.val) blocks.val ⦄ := by
  unfold X86RemainderRust.sha256.stream.remainder
  change (do let bmi ← ok bmi2Available
             if bmi then do
               let sha ← ok ChainWideRust.shaNiAvailable
               if sha then ArmStreamRust.sha2.sha256.compress256 st blocks else StreamScalarRust.sha256.stream.scalar st blocks
             else ArmStreamRust.sha2.sha256.compress256 st blocks) ⦃ out => _ ⦄
  cases bmi2Available <;> cases ChainWideRust.shaNiAvailable <;> simp only [bind_ok,Bool.false_eq_true,ite_false,ite_true] <;>
    first | exact PlatformStream.bulk256 st blocks | exact scalar256 st blocks

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
  unfold X86RemainderRust.sha512.stream.remainder
  change (do let bmi ← ok bmi2Available
             if bmi then do
               let sha ← ok ChainWideRust.shaNiAvailable
               if sha then ArmStreamRust.sha2.sha512.compress512 st blocks else StreamScalarRust.sha512.stream.scalar st blocks
             else ArmStreamRust.sha2.sha512.compress512 st blocks) ⦃ out => _ ⦄
  cases bmi2Available <;> cases ChainWideRust.shaNiAvailable <;> simp only [bind_ok,Bool.false_eq_true,ite_false,ite_true] <;>
    first | exact PlatformStream.bulk512 st blocks | exact scalar512 st blocks

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
