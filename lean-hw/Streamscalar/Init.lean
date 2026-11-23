import Streamscalar.Funs
import Streamstep.Transition
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

theorem initial256 (block : Array U8 64#usize) :
    core.array.from_fn 16#usize StreamScalarRust.sha256.stream.scalar.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 block
      ⦃ w => window (slots256 w) (Spec.SHA256.schedule (bytes block.val)) 0 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize _ block
    (fun i (x : U32) => x.bv = (Spec.SHA256.schedule (bytes block.val))[i]!) ?_)
  · intro w hw k _ hi
    have bound : k < 16 := by simpa using hi
    simpa [slots256,Nat.mod_eq_of_lt bound,Array.getElem!_Nat_eq] using hw k bound
  intro i hi
  unfold StreamScalarRust.sha256.stream.scalar.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  simp only [StreamScalarRust.sha256.stream.scalar.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut]
  step with read_word256 block i hi
  assumption

theorem initial512 (block : Array U8 128#usize) :
    core.array.from_fn 16#usize StreamScalarRust.sha512.stream.scalar.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 block
      ⦃ w => window (slots512 w) (Spec.SHA512.schedule (bytes block.val)) 0 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize _ block
    (fun i (x : U64) => x.bv = (Spec.SHA512.schedule (bytes block.val))[i]!) ?_)
  · intro w hw k _ hi
    have bound : k < 16 := by simpa using hi
    simpa [slots512,Nat.mod_eq_of_lt bound,Array.getElem!_Nat_eq] using hw k bound
  intro i hi
  unfold StreamScalarRust.sha512.stream.scalar.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  simp only [StreamScalarRust.sha512.stream.scalar.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut]
  step with read_word512 block i hi
  assumption

end slhdsa.X86.Stream
