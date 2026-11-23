import Chainavx2.Address
import Chainavx2.Registers
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

def storeWord (b : Spec.Bytes) (word count : Nat) (v : U32) :=
  b.take (22+4*word) ++ (Spec.toByte v.val 4).take count ++ b.drop (22+4*word+count)

/-- Every byte outside the word's selected digest prefix is preserved. -/
theorem word_store_spec (N lane : Usize) (it : core.ops.range.Range Usize)
    (batch : Batch) (digest : DigestWords) (hn : N.val ≤ 32) (hl : lane.val < 8)
    (active : it.start.val < it.end.val) (hw : 4*it.start.val < N.val) :
    chains_loop0_loop1_loop1_loop0.body N digest lane it batch ⦃ flow =>
      ∃ next r, flow = cont (next,r) ∧ next.start.val = it.start.val+1 ∧ next.end = it.end ∧
        (∀ j, j ≠ lane.val → r.val[j]! = batch.val[j]!) ∧
        bytes r.val[lane.val]!.val = storeWord (bytes batch.val[lane.val]!.val)
          it.start.val (min 4 (N.val-4*it.start.val)) (digest.val[it.start.val]!.val[lane.val]!) ⦄ := by
  unfold chains_loop0_loop1_loop1_loop0.body
  step with core.iter.range.IteratorRange.next_Usize_some_spec it active as ⟨o,next,ho,hnext,hend⟩
  simp only [ho]
  step as ⟨beginWord,hb⟩
  step as ⟨left,hleft⟩
  let count := core.cmp.impls.OrdUsize.min 4#usize left
  have hc : count.val = min 4 (N.val-4*it.start.val) := by
    change (if left < 4#usize then left else 4#usize).val = _
    split <;> rename_i h
    · rw [Nat.min_eq_right (by scalar_tac)]; scalar_tac
    · rw [Nat.min_eq_left (by scalar_tac)]; rfl
  simp only [lift,bind_tc_eq,bind_ok]
  step as ⟨pos,hp⟩
  step as ⟨a,back,ha,hback⟩
  step as ⟨stop,hstop⟩
  step as ⟨s,backA,hsub,hslen,hba⟩
  step as ⟨reg,hr⟩
  step as ⟨v,hv⟩
  step as ⟨src,hsrc,hsrcLen⟩
  step as ⟨dst,hd⟩
  all_goals try (change (core.cmp.impls.OrdUsize.min 4#usize left).val = _ at hc; scalar_tac)
  simp only [step_simps,hback,Array.set_val_eq]
  refine ⟨next,_,rfl,hnext,hend,?_,?_⟩
  · intro j hj; rw [Array.set_val_eq]; exact Avx2.setOther _ _ _ _ (Ne.symm hj)
  rw [Array.set_val_eq,Avx2.setSame _ _ _ (by scalar_tac),hd,hba,bytes_setSlice]
  · have val : v = digest.val[it.start.val]!.val[lane.val]! := by rw [hv,hr,← getElem!_pos,← getElem!_pos]
    have be : bytes (core.num.U32.to_be_bytes v).val = Spec.toByte v.val 4 := by
      simpa [core.num.U32.to_be_bytes,bytes] using Intel.Chain.big_endian v.bv
    have bs : bytes src.val = (Spec.toByte v.val 4).take count.val := by
      rw [hsrc]
      simp only [List.slice,Nat.sub_zero,List.drop_zero,Array.val_to_slice,bytes,List.map_take]
      exact congrArg (List.take count.val) be
    change (core.cmp.impls.OrdUsize.min 4#usize left).val = _ at hc
    rw [bs,show src.val.length = count.val from hsrcLen,ha,← getElem!_pos,hp,hb,val]
    simp only [storeWord,count,hc]
  · change (core.cmp.impls.OrdUsize.min 4#usize left).val = _ at hc
    scalar_tac
end slhdsa.Avx2.Chain
