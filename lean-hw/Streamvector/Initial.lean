import Streamvector.Funs
import Streamvector.Controls
open Aeneas Aeneas.Std Result
open core.core_arch.x86
namespace slhdsa.X86.Stream
open S512.Gather (flat flat_length)

def vectorWindow256 (w : Array __m512i 16#usize) (blocks : Array (Array U8 64#usize) 16#usize) (t : Nat) :=
  ∀ j : Fin 16, window (fun k => (w.val[k]!) j) (Spec.SHA256.schedule (bytes blocks.val[j.val]!.val)) t

theorem vectorInitial256 (blocks : Array (Array U8 64#usize) 16#usize) (offsets : __m512i)
    (stride : Digest.Stride offsets 64) :
    core.array.from_fn 16#usize StreamVectorRust.sha256.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i (blocks,offsets,Store.control)
      ⦃ w => vectorWindow256 w blocks 0 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize _ _
    (fun k x => ∀ j : Fin 16, x j = (Spec.SHA256.schedule (bytes blocks.val[j.val]!.val))[k]!) ?_)
  · intro w hw j k _ hi
    have bound : k < 16 := by simpa using hi
    simpa only [Nat.mod_eq_of_lt bound,Array.getElem!_Nat_eq] using hw k bound j
  intro k hk
  unfold StreamVectorRust.sha256.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i
  simp only [StreamVectorRust.sha256.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut,lift,bind_tc_eq,bind_ok,StreamVectorRust.core.slice.Slice.as_ptr,
    GatherRust.core.slice.Slice.as_ptr,StreamVectorRust.core.ptr.const_ptr.RawPtrConstT.cast,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,Array.val_to_slice]
  step as ⟨idx,hi⟩
  have total : (flat blocks.val).length = 1024 := by rw [flat_length]; simp
  have bound : idx.val ≤ (flat blocks.val).length := by rw [total,hi]; scalar_tac
  unfold flat at bound
  simp only [StreamVectorRust.core.ptr.const_ptr.RawPtrConstT.add,GatherRust.core.ptr.const_ptr.RawPtrConstT.add,
    Nat.zero_add,bound,ite_true,bind_ok,StreamVectorRust.core.core_arch.x86.avx512f._mm512_i32gather_epi32,
    StreamVectorRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8]
  have gather := gathered256 blocks offsets stride k.val hk
  have pos : idx.val = 4*k.val := by rw [hi,Nat.mul_comm]
  rw [pos]
  rw [← Std.bind_assoc]
  apply WP.spec_bind gather
  intro x hx
  exact (WP.spec_ok _).mpr ⟨hx,rfl⟩

def vectorWindow512 (w : Array __m512i 16#usize) (blocks : Array (Array U8 128#usize) 8#usize) (t : Nat) :=
  ∀ j : Fin 8, window (fun k => word64 (w.val[k]!) j) (Spec.SHA512.schedule (bytes blocks.val[j.val]!.val)) t

theorem vectorInitial512 (blocks : Array (Array U8 128#usize) 8#usize) (offsets : __m256i)
    (stride : S512.Gather.Stride offsets 128) :
    core.array.from_fn 16#usize StreamVectorRust.sha512.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i (blocks,offsets,S512.Gather.swapControl)
      ⦃ w => vectorWindow512 w blocks 0 ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize _ _
    (fun k x => ∀ j : Fin 8, word64 x j = (Spec.SHA512.schedule (bytes blocks.val[j.val]!.val))[k]!) ?_)
  · intro w hw j k _ hi
    have bound : k < 16 := by simpa using hi
    simpa only [Nat.mod_eq_of_lt bound,Array.getElem!_Nat_eq] using hw k bound j
  intro k hk
  unfold StreamVectorRust.sha512.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i
  simp only [StreamVectorRust.sha512.stream.prescheduled.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut,lift,bind_tc_eq,bind_ok,StreamVectorRust.core.slice.Slice.as_ptr,
    GatherRust.core.slice.Slice.as_ptr,StreamVectorRust.core.ptr.const_ptr.RawPtrConstT.cast,
    GatherRust.core.ptr.const_ptr.RawPtrConstT.cast,Array.val_to_slice]
  step as ⟨idx,hi⟩
  have total : (flat blocks.val).length = 1024 := by rw [flat_length]; simp
  have bound : idx.val ≤ (flat blocks.val).length := by rw [total,hi]; scalar_tac
  unfold flat at bound
  simp only [StreamVectorRust.core.ptr.const_ptr.RawPtrConstT.add,GatherRust.core.ptr.const_ptr.RawPtrConstT.add,
    Nat.zero_add,bound,ite_true,bind_ok,StreamVectorRust.core.core_arch.x86.avx512f._mm512_i32gather_epi64,
    StreamVectorRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8]
  have gather := gathered512 blocks offsets stride k.val hk
  have pos : idx.val = 8*k.val := by rw [hi,Nat.mul_comm]
  rw [pos]
  rw [← Std.bind_assoc]
  apply WP.spec_bind gather
  intro x hx
  exact (WP.spec_ok _).mpr ⟨hx,rfl⟩

end slhdsa.X86.Stream
