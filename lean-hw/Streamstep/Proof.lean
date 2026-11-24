import Streamstep.Funs
import Streamround.Read
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

theorem read_word256 (block : Array U8 64#usize) (i : Usize) (bound : i.val < 16) :
    StreamStepRust.sha256.stream.read_word block i ⦃ x =>
      x.bv = (Spec.SHA256.schedule (bytes block.val))[i.val]! ⦄ := by
  unfold StreamStepRust.sha256.stream.read_word
  step*
  · cases r with
    | Ok a => exact ⟨a,rfl⟩
    | Err e => cases e; simp only at r_post; omega
  · apply load256 block i.val bound
    simp_all [Array.val_to_slice,List.slice,Nat.mul_add,Nat.mul_comm]

theorem read_word512 (block : Array U8 128#usize) (i : Usize) (bound : i.val < 16) :
    StreamStepRust.sha512.stream.read_word block i ⦃ x =>
      x.bv = (Spec.SHA512.schedule (bytes block.val))[i.val]! ⦄ := by
  unfold StreamStepRust.sha512.stream.read_word
  step*
  · cases r with
    | Ok a => exact ⟨a,rfl⟩
    | Err e => cases e; simp only at r_post; omega
  · apply load512 block i.val bound
    simp_all [Array.val_to_slice,List.slice,Nat.mul_add,Nat.mul_comm]

end slhdsa.X86.Stream
