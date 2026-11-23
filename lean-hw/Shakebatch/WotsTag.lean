import Shakebatch.WotsChainProgram
import Shakebatch.Put
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def wordTag (x : U32) : BitVec 64 :=
  ((x.bv.extractLsb' 0 8 ++ x.bv.extractLsb' 8 8 ++ x.bv.extractLsb' 16 8 ++ x.bv.extractLsb' 24 8).zeroExtend 64) <<< 32

theorem chain_tag (s : Matrix machine.width) (offset : Usize) (index : Array U32 machine.width)
    (pos : 0<offset.val) (room : offset.val ≤ 25) :
    shake.batch.chains_loop0_loop0 ⟨0#usize,machine.width⟩ index offset s ⦃ out =>
      ∀ k < 25, ∀ j < machine.width.val, cell out k j =
        if k=offset.val-1 then cell s k j ||| wordTag index.val[j]! else cell s k j ⦄ := by
  unfold shake.batch.chains_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => machine.width.val-q.1.start.val)
    (inv := fun q => q.1.end=machine.width ∧ q.1.start.val ≤ machine.width.val ∧
      ∀ k < 25, ∀ j < machine.width.val, cell q.2 k j =
        if k=offset.val-1 ∧ j<q.1.start.val then cell s k j ||| wordTag index.val[j]! else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold shake.batch.chains_loop0_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < machine.width.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step as ⟨ix,get⟩
      simp only [core.num.U32.swap_bytes,bind_ok,lift]
      step as ⟨tag,tagval,tagbv⟩
      step as ⟨row,rval⟩ <;> try scalar_tac
      step as ⟨old,oldrow⟩
      step as ⟨previous,oldval⟩
      try simp only [lift,bind_ok]
      step as ⟨a,back,read,write⟩
      step as ⟨a',update⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write,update,read,← getElem!_pos,cell_write _ _ _ _ (by omega) lt,rval,h k hk j hj]
      by_cases target : k=offset.val-1
      · subst k
        by_cases here : j=it.start.val
        · subst j
          simp only [true_and,ite_true,hn,Nat.lt_add_one,ite_false,lt_self_iff_false]
          have before := h row.val (by omega) it.start.val lt
          simp only [lt_self_iff_false,and_false,ite_false] at before
          rw [← rval,← before]
          simp only [cell]
          rw [oldval,oldrow,← getElem!_pos,← getElem!_pos]
          change _ ||| tag.bv = _ ||| _
          apply congrArg (fun z : BitVec 64 => cell state row.val it.start.val ||| z)
          apply Eq.trans tagbv
          rw [get,← getElem!_pos]
          rfl
        · have same : j < nxt.start.val ↔ j < it.start.val := by omega
          simp [here,same]
      · simp [target]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=machine.width.val := by rw [he] at more; omega
      intro k hk j hj
      simpa [eq,hj] using h k hk j hj
  · simp

end slhdsa.ShakeBatch
