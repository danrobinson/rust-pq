import S8table.Gather
import S8word.Proof
import Streamvector.Initial
open Aeneas Aeneas.Std Result
open core.core_arch.x86
namespace slhdsa.X86.Stream.Eight
open S512.Gather (flat flat_length)
theorem initial (blocks : Array (Array U8 64#usize) 8#usize) (offsets : __m256i)
    (hs : stride offsets) :
    core.array.from_fn 16#usize S8tableRust.sha256.stream.schedule.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m256i (blocks,offsets,control)
      ⦃ w => ring w (fun j => Spec.SHA256.schedule (bytes blocks.val[j.val]!.val)) 0 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize _ _
    (fun k x => ∀ j : Fin 8, x j = (Spec.SHA256.schedule (bytes blocks.val[j.val]!.val))[k]!) ?_)
  · intro w hw k _ hi j
    have bound : k < 16 := by simpa using hi
    simpa only [Nat.mod_eq_of_lt bound,Array.getElem!_Nat_eq] using hw k bound j
  intro k hk
  unfold S8tableRust.sha256.stream.schedule.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m256i
  simp only [S8tableRust.sha256.stream.schedule.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m256i.call_mut,lift,bind_tc_eq,bind_ok,S8tableRust.core.slice.Slice.as_ptr,
    GatherRust.core.slice.Slice.as_ptr,S8tableRust.core.ptr.const_ptr.RawPtrConstT.cast,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,Array.val_to_slice]
  step as ⟨idx,hi⟩
  have total : (flat blocks.val).length = 512 := by rw [flat_length]; simp
  have bound : idx.val ≤ (flat blocks.val).length := by rw [total,hi]; scalar_tac
  unfold flat at bound
  simp only [S8tableRust.core.ptr.const_ptr.RawPtrConstT.add,GatherRust.core.ptr.const_ptr.RawPtrConstT.add,
    Nat.zero_add,bound,ite_true,bind_ok]
  have gather := gathered blocks offsets hs k.val hk
  have pos : idx.val = 4*k.val := by rw [hi,Nat.mul_comm]
  rw [pos]
  rw [← Std.bind_assoc]
  apply WP.spec_bind gather
  intro x hx
  exact (WP.spec_ok _).mpr ⟨hx,rfl⟩

end slhdsa.X86.Stream.Eight
