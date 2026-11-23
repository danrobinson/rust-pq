import Gather512.Block
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather
open GatherRust.sha512.x86
open _root_.core.core_arch.x86

def hashed (seed : List (BitVec 64)) (data : Spec.Bytes) (n : Nat) :=
  (List.range n).foldl (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt data k)) seed

private theorem next_hash (seed : List (BitVec 64)) (data : Spec.Bytes) (n : Nat) :
    hashed seed data (n+1) = Spec.SHA512.compress (hashed seed data n) (Spec.SHA512.blockAt data n) := by
  simp [hashed,List.range_succ,List.foldl_append]

theorem hash_spec (N L : Usize) (rows : Slice (Array U8 L)) (mask : U8) (stride : __m256i)
    (init : Array Reg 8#usize) (seed : List (BitVec 64)) (hinit : ∀ j, stateWords (laneState init j) = seed)
    (hm : Mask mask rows.length) (hs : Stride stride L.val) (hn : 0 < rows.length) (hl : L.val % 128 = 0) :
    digest_groups_loop0 N ⟨⟨0#usize,L⟩,128#usize⟩ rows mask init stride swapControl ⦃ r =>
      ∀ j : Fin 8, j.val < rows.length → stateWords (laneState r j) = hashed seed (bytes rows.val[j.val]!.val) (L.val/128) ⦄ := by
  unfold digest_groups_loop0
  apply loop.spec_decr_nat (measure := fun p : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize) × Array Reg 8#usize =>
      L.val-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end = L ∧ p.1.step_by = 128#usize ∧ p.1.iter.start.val ≤ L.val ∧
      p.1.iter.start.val % 128 = 0 ∧ ∀ j : Fin 8, j.val < rows.length → stateWords (laneState p.2 j) =
        hashed seed (bytes rows.val[j.val]!.val) (p.1.iter.start.val/128))
  · rintro ⟨it,state⟩ ⟨he,hstep,hbound,hdiv,hstate⟩
    simp only at he hstep hbound hdiv hstate
    unfold digest_groups_loop0.body
    by_cases hlt : it.iter.start.val < it.iter.end.val
    · have hoff : it.iter.start.val + 128 ≤ L.val := by rw [he] at hlt; omega
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_some_spec it hlt
        (by rw [hstep]; decide) (by rw [he,hstep]; exact hoff) as ⟨o,it',ho,hstart,hend,hstride⟩
      simp only [ho]
      step with words_spec N L rows mask stride it.iter.start hm hs hn hoff as ⟨w,hw⟩
      rw [compress_eq]
      step with compress_block_spec state w _ hw as ⟨r,hr⟩
      have hinc : it'.iter.start.val = it.iter.start.val+128 := by rw [hstart,hstep]; rfl
      refine ⟨hend.trans he,hstride.trans hstep,by omega,by omega,?_,by omega⟩
      intro j hj
      rw [hr,hstate j hj, show it'.iter.start.val/128 = it.iter.start.val/128+1 by omega,next_hash]
      simp [laneBlock,hj,Spec.SHA512.blockAt,List.slice,show 128*(it.iter.start.val/128) = it.iter.start.val by omega]
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,it',ho,hit⟩
      simp only [ho,step_simps]
      have heq : it.iter.start.val = L.val := by rw [he] at hlt; omega
      simpa [heq] using hstate
  · simp [hashed,hinit]

#print axioms hash_spec
end slhdsa.X86.S512.Gather
