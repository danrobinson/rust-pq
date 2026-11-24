import Kgridbulk.Memory
import Slhdsa.Proofs.Basic
import Spec.SlhDsa
open Aeneas Aeneas.Std Result
namespace slhdsa.Kgridbulk
open KgridbulkRust KgridbulkRust.shake256.stream_x86
abbrev Row := KgridbulkRust.core.core_arch.x86.__m512i

private theorem stateLoad (s : Array U64 25#usize) (y : Usize) (hy : y.val<5) :
    absorb.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut s y ⦃ r =>
      r.2 = s ∧ ∀ j : Fin 8, j.val < 5 → r.1 j = s.val[5*y.val+j.val]!.bv ⦄ := by
  let mem := s.val.flatMap (ChainWideRust.MemoryElement.encode (T := U64))
  have len : mem.length=200 := by
    unfold mem
    have h (ws : List U64) : (ws.flatMap (ChainWideRust.MemoryElement.encode (T := U64))).length=8*ws.length := by
      induction ws with
      | nil => rfl
      | cons w ws ih =>
        have hw : (ChainWideRust.MemoryElement.encode w).length=8 := by
          change (w.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).length=8
          simp
        simp only [List.flatMap_cons,List.length_append,hw,ih,List.length_cons]
        omega
    rw [h]
    simp
  unfold absorb.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
  simp only [lift,core.slice.Slice.as_ptr,ChainWideRust.core.slice.Slice.as_ptr,bind_ok,Array.val_to_slice]
  step as ⟨idx,hidx⟩
  have off : idx.val*8 ≤ mem.length := by rw [len]; scalar_tac
  simp only [core.ptr.const_ptr.RawPtrConstT.add,ChainWideRust.core.ptr.const_ptr.RawPtrConstT.add,
    Nat.zero_add,show ChainWideRust.MemoryElement.width U64=8 by rfl,if_pos off,bind_ok,
    core.ptr.const_ptr.RawPtrConstT.cast,GatherRust.core.ptr.const_ptr.RawPtrConstT.cast]
  rw [if_pos off]
  simp only [bind_ok, GatherRust.core.ptr.const_ptr.RawPtrConstT.cast]
  rw [loadFive _ (by change idx.val*8 + 40 ≤ mem.length; rw [len]; scalar_tac)]
  simp only [bind_ok,step_simps]
  intro j hj
  rw [if_pos hj]
  change wordAt mem (idx.val*8 + 8*j.val) = _
  rw [show idx.val*8+8*j.val=8*(5*y.val+j.val) by scalar_tac]
  exact readStateWord _ _ (by simp; omega)

theorem pack (s : Array U64 25#usize) :
    core.array.from_fn 5#usize absorb.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i s
      ⦃ out => ∀ y : Nat, y<5 → ∀ j : Fin 8, j.val<5 → out.val[y]! j = s.val[5*y+j.val]!.bv ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 5#usize _ _
    (fun y (row : Row) => ∀ j : Fin 8, j.val<5 → row j = s.val[5*y+j.val]!.bv) ?_)
  · intro out h
    intro y hy j hj
    simpa only [Array.getElem!_Nat_eq] using h y hy j hj
  intro i hi
  exact WP.spec_mono (stateLoad s i hi) (by rintro ⟨r,g⟩ h; exact ⟨h.2,h.1⟩)
end slhdsa.Kgridbulk
