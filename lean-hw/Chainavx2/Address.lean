import Chainavx2.Lengths
import Chainni.Words
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2
open Intel.Chain (withIndex big_endian)
abbrev Batch := Array (Array U8 64#usize) 8#usize

def putAddress (batch : Batch) (starts : Slice U32) (off lane : Usize) (step : U32) := do
  let (a,back) ← Array.index_mut_usize batch lane
  let (s,backA) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) a (⟨18#usize,22#usize⟩ : core.ops.range.Range Usize)
  let pos ← off + lane
  let t ← Slice.index_usize starts pos
  let index ← t + step
  let src ← lift (Array.to_slice (core.num.U32.to_be_bytes index))
  let dst ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back (backA dst))

theorem put_address_spec (batch : Batch) (starts : Slice U32) (off lane : Usize) (step : U32)
    (hi : lane.val < 8) (hs : off.val+lane.val < starts.length)
    (bound : starts.val[off.val+lane.val]!.val+step.val ≤ U32.max) :
    putAddress batch starts off lane step ⦃ r =>
      (∀ j, j ≠ lane.val → r.val[j]! = batch.val[j]!) ∧
      bytes r.val[lane.val]!.val = withIndex (bytes batch.val[lane.val]!.val)
        (starts.val[off.val+lane.val]!.val+step.val) ⦄ := by
  unfold putAddress
  have ub := starts.property
  step as ⟨ab,ha,hback⟩
  obtain ⟨a,back⟩ := ab
  step as ⟨sb,hsub,hslen,hba⟩
  obtain ⟨s,backA⟩ := sb
  simp only at ha hback hsub hslen hba
  step as ⟨pos,hp⟩
  step as ⟨t,ht⟩
  have ht' : t = starts.val[off.val+lane.val]! := by rw [ht,← getElem!_pos,hp]
  step as ⟨index,hindex⟩
  simp only [lift,bind_tc_eq,bind_ok]
  step as ⟨dst,hd⟩
  all_goals try (simp only [Slice.length] at *; scalar_tac)
  simp only [step_simps,hback,Array.set_val_eq]
  refine ⟨fun j hj => Avx2.setOther _ _ _ _ (Ne.symm hj),?_⟩
  rw [Avx2.setSame _ _ _ (by scalar_tac),hd,hba,bytes_setSlice]
  · simp only [Array.val_to_slice,ha,← getElem!_pos,withIndex]
    have be : bytes (core.num.U32.to_be_bytes index).val = Spec.toByte index.val 4 := by
      simpa [core.num.U32.to_be_bytes,bytes] using big_endian index.bv
    rw [be,hindex,ht']
    simp
  · simp

theorem addresses_spec (batch : Batch) (starts : Slice U32) (off : Usize) (lengths : Array U32 8#usize)
    (step : U32) (hs : off.val+8 ≤ starts.length)
    (safe : ∀ j < 8, step.val < lengths.val[j]!.val → starts.val[off.val+j]!.val+step.val ≤ U32.max) :
    chains_loop0_loop1_loop0 ⟨0#usize,8#usize⟩ starts batch off lengths step ⦃ r =>
      ∀ j < 8, bytes r.val[j]!.val = if step.val < lengths.val[j]!.val then
        withIndex (bytes batch.val[j]!.val) (starts.val[off.val+j]!.val+step.val) else bytes batch.val[j]!.val ⦄ := by
  unfold chains_loop0_loop1_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Batch => 8-p.1.start.val)
    (inv := fun p => p.1.end.val = 8 ∧ p.1.start.val ≤ 8 ∧ ∀ j < 8, bytes p.2.val[j]!.val =
      if j < p.1.start.val ∧ step.val < lengths.val[j]!.val then
        withIndex (bytes batch.val[j]!.val) (starts.val[off.val+j]!.val+step.val) else bytes batch.val[j]!.val)
  · rintro ⟨it,rows⟩ ⟨he,hi,inv⟩
    simp only at he hi inv
    unfold chains_loop0_loop1_loop0.body
    by_cases lt : it.start.val < it.end.val
    · have h8 : it.start.val < 8 := by omega
      step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hn,hend⟩
      simp only [ho]
      step as ⟨len,hl⟩
      have hl' : len = lengths.val[it.start.val]! := by rw [hl,getElem!_pos]
      by_cases live : step < len
      · simp only [if_pos live]
        have active : step.val < lengths.val[it.start.val]!.val := hl' ▸ live
        conv => lhs; equals (putAddress rows starts off it.start step >>= fun r => ok (cont (next,r))) =>
          unfold putAddress
          simp only [lift,bind_ok,Std.bind_assoc,bind_tc_eq]
          rfl
        step with put_address_spec rows starts off it.start step h8 (by omega) (safe _ h8 active) as ⟨r,other,here⟩
        refine ⟨by rw [hend,he],by omega,?_,by omega⟩
        intro j hj
        by_cases same : j = it.start.val
        · subst j
          rw [here,inv _ h8]
          simp only [active,show it.start.val < next.start.val by omega,Nat.lt_irrefl,and_self,
            false_and,ite_true,ite_false]
        · rw [other _ same,inv j hj]
          have eq : j < next.start.val ↔ j < it.start.val := by omega
          simp only [eq]
      · simp only [if_neg live,step_simps]
        refine ⟨by rw [hend,he],by omega,?_,by omega⟩
        intro j hj
        rw [inv j hj]
        by_cases same : j = it.start.val
        · subst j
          have inactive : ¬ step.val < lengths.val[it.start.val]!.val := hl' ▸ live
          simp only [inactive,and_false,ite_false]
        · have eq : j < next.start.val ↔ j < it.start.val := by omega
          simp only [eq]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      intro j hj
      simpa only [show j < it.start.val by omega,true_and] using inv j hj
  · simp
end slhdsa.Avx2.Chain
