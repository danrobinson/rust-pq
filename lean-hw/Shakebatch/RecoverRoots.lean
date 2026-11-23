import Shakebatch.LeafStart
import Shakebatch.RecoverClimb
import Shakebatch.RecoverStream
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [ok : StreamCorrect]
private abbrev Steps := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

set_option maxHeartbeats 2500000 in
theorem recover_roots {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig : Slice U8)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (seed : Array U8 N) (a : address.Adrs)
    (perms : PermutationCorrect) (enabled : 0 < machine.width.val)
    (choices : Slice U32) (count : choices.length=p.k.val)
    (index : ∀ j < choices.length, choices.val[j]!.val < 2^p.a.val)
    (stride : Usize) (str : stride.val=p.a.val+1) (state : stream.State)
    (base : Spec.Bytes) (prior : ok.Absorbed state base) (it : Steps)
    (width : it.step_by=machine.width) (init : it.iter=⟨0#usize,choices.len⟩) :
    shake.fors_batch.recover_loop0 it p.n p.h p.d p.hp p.a p.k p.m choices sig seed a.layer a.tree
      a.typ a.keypair a.word2 a.word3 stride state ⦃ out => ok.Absorbed out (base ++
        (List.range p.k.val).flatMap (forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val)
          (adrsS a) (nats choices.val))) ⦄ := by
  let root := forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) (nats choices.val)
  have hk : choices.length ≤ 35 := count.symm ▸ hp.valid.k_le
  unfold shake.fors_batch.recover_loop0
  apply loop.spec_decr_nat (measure := fun q : Steps × stream.State => choices.length-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end.val=choices.length ∧ q.1.step_by=machine.width ∧
      q.1.iter.start.val ≤ choices.length ∧ ok.Absorbed q.2 (base ++ (List.range q.1.iter.start.val).flatMap root))
  · rintro ⟨iter,cur⟩ ⟨he,hs,hi,old⟩
    simp only at he hs hi old
    unfold shake.fors_batch.recover_loop0.body
    step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter (by rw [hs];exact enabled)
      as ⟨o,nxt,splitNext,hend,hwidth⟩
    by_cases more : iter.iter.start.val < iter.iter.end.val
    · simp only [if_pos more] at splitNext
      obtain ⟨some,advance⟩ := splitNext
      simp only [some]
      step as ⟨rem,remaining⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min rem machine.width
      have av : active.val=min (choices.length-iter.iter.start.val) machine.width.val := by
        simp [active,core.cmp.impls.OrdUsize.min_val,remaining]
      have fw : iter.iter.start.val+active.val ≤ choices.length := by omega
      have widthBound : active.val ≤ machine.width.val := by omega
      have az : 0 < active.val := by omega
      have same : nxt.iter.start.val=iter.iter.start.val+active.val := by rw [advance,hs,he,av];omega
      step with recover_trees N iter.iter.start active az (by scalar_tac) as ⟨trees,tree⟩
      have valid (j : Nat) (hj : j < machine.width.val) : trees.val[j]!.val < choices.length := by
        rw [tree j hj]; change iter.iter.start.val+min j (active.val-1) < choices.length;omega
      step with recover_indices p hp choices trees hk valid index as ⟨idx,selected⟩
      step with recover_secrets p hp sig len stride str trees (fun j hj => count ▸ valid j hj) as ⟨secrets,keys⟩
      step with recover_leaf_addresses N a idx as ⟨addrs,addressed⟩
      step with short_fips seed addrs secrets perms hp.le32 (aligned_hash hp) as ⟨leaves,leaf⟩
      have start (j : Nat) (hj : j < machine.width.val) :
          AtLevel (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) (nats choices.val)
            trees.val[j]!.val 0 idx.val[j]!.val (bytes leaves.val[j]!.val) := by
        apply leaf_start p hp sig seed a (nats choices.val) trees.val[j]!.val idx.val[j]!
          (by rw [selected j hj,fors_nats_getElem! _ _ (valid j hj),getElem!_pos choices.val _ (valid j hj)]) secrets.val[j]! leaves.val[j]!
          (keys j hj)
        rw [leaf j hj,addressed j hj]
      step with recover_climb p hp sig len seed a perms stride str trees (fun j hj => count ▸ valid j hj)
        (nats choices.val) idx leaves start as ⟨vals,roots⟩
      step as ⟨s,sub⟩
      have ss : s.val=vals.val.take active.val := by simpa only [active,List.slice_zero_j,Array.val_to_slice] using sub
      have slen : s.length=active.val := by simp [Slice.length,ss];omega
      simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
      have values (j : Nat) (hj : j < s.length) : bytes s.val[j]!.val=root (iter.iter.start.val+j) := by
        have inWidth : j < machine.width.val := by omega
        have ht : j < (vals.val.take active.val).length := by rw [← ss];exact hj
        rw [ss,getElem!_pos (vals.val.take active.val) j ht,List.getElem_take,← getElem!_pos vals.val j,roots j inWidth,tree j inWidth]
        have eq : treeAt iter.iter.start.val active.val j=iter.iter.start.val+j := by unfold treeAt;omega
        rw [eq]
      step with absorb_roots s cur base iter.iter.start.val root old values as ⟨out,hout⟩
      exact ⟨by rw [hend,he],hwidth.trans hs,by omega,by simpa only [same,slen] using hout,by omega⟩
    · simp only [if_neg more] at splitNext
      simp only [splitNext.1,step_simps]
      have eq : iter.iter.start.val=p.k.val := by omega
      simpa only [eq] using old
  · simp [init,width,prior]

end slhdsa.ShakeBatch
