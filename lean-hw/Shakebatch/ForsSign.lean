import Shakebatch.SigPrefix
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
private abbrev Steps := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

theorem sign_prefix {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (choices : Slice U32) (permutes : PermutationCorrect)
    (enabled : 0 < machine.width.val) (count : choices.length=p.k.val)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    shake.fors_batch.sign p choices sk seed a ⦃ out =>
      SigPrefix p sk seed a choices ((p.a.val+1)*N.val) choices.length out ⦄ := by
  have ha : p.a.val ≤ 14 := hp.valid.a_le
  have hk : choices.length ≤ 35 := count.symm ▸ hp.valid.k_le
  have hn := hp.le32
  have pos := hp.nok.ge16
  have strideBound := Nat.mul_le_mul (show p.a.val+1 ≤ 15 by omega) hn
  have bufferBound := Nat.mul_le_mul hk strideBound
  unfold shake.fors_batch.sign
  simp only [lift,bind_ok]
  have castValue : (UScalar.cast .Usize p.a).val=p.a.val := by scalar_tac
  step as ⟨n,plus⟩
  step as ⟨stride,st⟩
  have shape : stride.val=(p.a.val+1)*N.val := by rw [st,plus,castValue]
  have fits : choices.length*stride.val ≤ Usize.max := by rw [shape];scalar_tac
  step as ⟨size,sz⟩
  all_goals try scalar_tac
  step as ⟨buf,zeros,len⟩
  step as ⟨it,init,iwidth⟩
  unfold shake.fors_batch.sign_loop0
  apply loop.spec_decr_nat (measure := fun q : Steps × Buffer => choices.length-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end.val=choices.length ∧ q.1.step_by=machine.width ∧
      q.1.iter.start.val ≤ choices.length ∧ SigPrefix p sk seed a choices stride.val q.1.iter.start.val q.2)
  · rintro ⟨iter,cur⟩ ⟨he,hs,hi,prior⟩
    simp only at he hs hi prior
    unfold shake.fors_batch.sign_loop0.body
    step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter (by rw [hs];exact enabled)
      as ⟨o,nxt,splitNext,hend,hwidth⟩
    by_cases more : iter.iter.start.val < iter.iter.end.val
    · simp only [if_pos more] at splitNext
      obtain ⟨some,advance⟩ := splitNext
      simp only [some]
      step as ⟨rem,remaining⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min rem machine.width
      have av : active.val = min (choices.length-iter.iter.start.val) machine.width.val := by
        simp [active,core.cmp.impls.OrdUsize.min_val,remaining]
      have fw : iter.iter.start.val+active.val ≤ choices.length := by omega
      have width : active.val ≤ machine.width.val := by omega
      have az : 0 < active.val := by omega
      have same : nxt.iter.start.val=iter.iter.start.val+active.val := by rw [advance,hs,he,av];omega
      step with selected p hp choices iter.iter.start active az fw hk index as ⟨ids,addr⟩
      step with fors_secrets p hp sk seed a ids permutes as ⟨secrets,sec⟩
      have fit : (iter.iter.start.val+active.val)*stride.val ≤ cur.length := by
        rw [prior.1];exact Nat.mul_le_mul_right _ fw
      step with write_secrets secrets iter.iter.start stride active cur fit width (by omega)
        (by rw [shape,Nat.add_mul,Nat.one_mul];omega) as ⟨once,store⟩
      have bounds (z : Nat) (hz : z < p.a.val) (j : Nat) (hj : j < machine.width.val) :
          (((ids.val[j]!.val/2^z) ^^^ 1)+1)*2^z < 2^32 := by
        let t := treeAt iter.iter.start.val active.val j
        have tr : t < choices.length := by change iter.iter.start.val+min j (active.val-1) < choices.length;omega
        rw [addr j hj,sibling_eq _ _ _ _ hz]
        exact (fors_inner_arith p.a.val t choices.val[t]!.val z ha (by omega) (index t tr) hz).2.2
      step with write_auth p hp sk seed a once stride iter.iter.start active ids permutes
        (store.1.symm ▸ fit) width shape bounds as ⟨out,path⟩
      have rowIndex (j : Nat) (hj : j < active.val) := addr j (by omega)
      refine ⟨hend ▸ he,hwidth.trans hs,by omega,?_,by omega⟩
      rw [same]
      apply batch_done p sk seed a choices _ _ _ ids secrets cur once out shape fw width prior _ sec store path
      intro j hj
      have row : treeAt iter.iter.start.val active.val j=iter.iter.start.val+j := by unfold treeAt;rw [min_eq_left (by omega)]
      dsimp only [active] at row
      simpa only [row] using rowIndex j hj
    · simp only [if_neg more] at splitNext
      simp only [splitNext.1,step_simps]
      have eq : iter.iter.start.val=choices.length := by omega
      simpa only [eq,shape] using prior
  · simp [init,iwidth,shape,SigPrefix,len,sz,st,plus,castValue]

end slhdsa.ShakeBatch
