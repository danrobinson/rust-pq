import Shakebatch.Program
import Shakeabs.Word

open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

/-- The word loaded by the batch packer has the byte order of the FIPS 202 lanes. -/
theorem word_spec (input : Slice U8) (i : Usize) (bound : i.val*8+8 ≤ input.length) :
    shake.batch.word input i ⦃ w => w.bv =
      Spec.Keccak.laneBytes 0 (bytes ((input.val.drop (i.val*8)).take 8)) ⦄ := by
  unfold shake.batch.word
  step as ⟨atWord,pos⟩
  step as ⟨last,stop⟩
  step as ⟨s,contents,count⟩
  have eight : s.length=(8#usize).val := by scalar_tac
  simp only [core.array.TryFromArrayCopySlice.try_from,eight,_root_.dite_true,core.result.Result.unwrap,
    bind_ok,step_simps,PlatformShake.loaded,Array.from_val]
  simp [contents,List.slice,pos,stop]

end slhdsa.ShakeBatch
