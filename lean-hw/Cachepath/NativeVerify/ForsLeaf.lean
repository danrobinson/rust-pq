import Cachepath.NativeVerify.ForsRows

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

def blockWords (sig : Slice U8) (size blockIndex : Nat) := inputWord ((sig.val.drop (blockIndex*size)).take size)

theorem leaf_lanes (N : Usize) (sig : Slice U8) (n offset stride first active : Usize)
    (s : Matrix machine.width) (indices : Array U32 machine.width)
    (size : n.val*8=N.val) (offsetEq : offset.val=n.val+4) (small : n.val≤4)
    (width : active.val≤machine.width.val) (stridePos : 0<stride.val)
    (fits : (first.val+active.val)*stride.val*N.val ≤ sig.length) (npos : 0<N.val) :
    recover_loop0_loop2 N ⟨0#usize,active⟩ sig n offset stride s first indices ⦃ out =>
      ∀ k<25, ∀ j<machine.width.val, cell out k j = if j<active.val then
        if k=n.val+3 then wordTag indices.val[j]! else
        if offset.val≤k ∧ k<offset.val+n.val then blockWords sig N.val ((first.val+j)*stride.val) (k-offset.val)
        else cell s k j
      else cell s k j ⦄ := by
  unfold recover_loop0_loop2
  apply range_fold (recover_loop0_loop2.body N sig n offset stride first indices) active s (fun count out =>
    ∀ k<25, ∀ j<machine.width.val, cell out k j = if j<count then
      if k=n.val+3 then wordTag indices.val[j]! else
      if offset.val≤k ∧ k<offset.val+n.val then blockWords sig N.val ((first.val+j)*stride.val) (k-offset.val)
      else cell s k j
    else cell s k j)
  · simp
  · intro it st stop live prev
    unfold recover_loop0_loop2.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨idx,idxRead⟩
    simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
    step as ⟨hi,_,hiEq⟩
    have tagVal : hi.bv=wordTag indices.val[it.start.val]! := by rw [idxRead,← getElem!_pos] at hiEq; exact hiEq
    step as ⟨r,rv⟩
    step as ⟨row,restore,read,back⟩
    step as ⟨row',upd⟩
    have treeBound : (first.val+it.start.val)*stride.val+1 ≤ (first.val+active.val)*stride.val := by
      have h := Nat.mul_le_mul_right stride.val (show (first.val+it.start.val)+1 ≤ first.val+active.val by omega)
      rw [Nat.add_mul,one_mul] at h
      omega
    have blockFit := (Nat.mul_le_mul_right N.val treeBound).trans fits
    have maxN : sig.length ≤ Usize.max := by simp
    have mulDom (v : Nat) : v ≤ v*N.val := by simpa using (Nat.mul_le_mul_left v npos)
    have treeDom := (show first.val+it.start.val ≤ (first.val+it.start.val)*stride.val by
      simpa using Nat.mul_le_mul_left (first.val+it.start.val) stridePos)
    have blockDom := mulDom ((first.val+it.start.val)*stride.val+1)
    have rawFit := blockFit
    rw [Nat.add_mul,one_mul] at rawFit
    step as ⟨tree,tv⟩
    step as ⟨block,bv⟩
    have posOk : block.val*N.val≤Usize.max := by rw [bv,tv]; omega
    step as ⟨pos,pv⟩
    step as ⟨same,sv⟩
    step as ⟨endBlock,ev⟩
    have epOk : endBlock.val*N.val≤sig.length := by rw [ev,sv,tv]; exact blockFit
    step as ⟨endPos,ep⟩
    have fitPos : pos.val+N.val=endPos.val := by rw [pv,bv,ep,ev,sv]; ring
    step as ⟨part,partBytes,partLen⟩
    step with leaf_payload (restore row') n offset it.start part (by omega) (by omega) (by omega) as ⟨out,write⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    intro k hk j hj
    rw [write k hk j hj,back,upd,read,← getElem!_pos,cell_write _ _ _ _ (by omega) (by omega),prev k hk j hj,tagVal,rv,inc]
    by_cases sameLane : j=it.start.val
    · subst j
      simp only [lt_self_iff_false,ite_false,Nat.lt_add_one,le_refl,ite_true,true_and,and_true]
      by_cases addr : k=n.val+3
      · simp [addr,offsetEq]
      · simp only [addr,ite_false]
        split
        · unfold blockWords
          rw [partBytes]
          simp only [List.slice,← fitPos,Nat.add_sub_cancel_left,pv,bv,tv]
        · rfl
    · simp only [sameLane,false_and,and_false,ite_false]
      rw [if_congr (show (j < it.start.val) ↔ j < it.start.val+1 by omega) rfl rfl]
  · intro it st last stop
    unfold recover_loop0_loop2.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Fors
