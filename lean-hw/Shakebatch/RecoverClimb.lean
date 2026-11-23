import Shakebatch.ClimbStep
import Shakebatch.RecoverBlocks
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem recover_climb {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig : Slice U8)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (seed : Array U8 N) (a : address.Adrs)
    (perms : PermutationCorrect) (stride : Usize) (hs : stride.val=p.a.val+1)
    (trees : Array Usize machine.width) (valid : ∀ j < machine.width.val, trees.val[j]!.val < p.k.val)
    (ind : List Nat) (initial : Array U32 machine.width) (leaves : Array (Array U8 N) machine.width)
    (start : ∀ j < machine.width.val, AtLevel (Shake.params p) (bytes sig.val) (bytes seed.val)
      (adrsS a) ind trees.val[j]!.val 0 initial.val[j]!.val (bytes leaves.val[j]!.val)) :
    shake.fors_batch.recover_loop0_loop0 ⟨0#u32,p.a⟩ sig seed a.layer a.tree a.typ a.keypair a.word2
      a.word3 stride trees initial leaves ⦃ out => ∀ j < machine.width.val, bytes out.val[j]!.val =
        forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) ind trees.val[j]!.val ⦄ := by
  unfold shake.fors_batch.recover_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range U32 × Array U32 machine.width ×
      Array (Array U8 N) machine.width => p.a.val-q.1.start.val)
    (inv := fun q => q.1.end=p.a ∧ q.1.start.val ≤ p.a.val ∧ ∀ j < machine.width.val,
      AtLevel (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) ind trees.val[j]!.val
        q.1.start.val q.2.1.val[j]!.val (bytes q.2.2.val[j]!.val))
  · rintro ⟨it,idx,v⟩ ⟨he,hi,prior⟩
    simp only at he hi prior
    unfold shake.fors_batch.recover_loop0_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < p.a.val := he ▸ more
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with recover_siblings p hp sig len stride hs it.start lt trees valid as ⟨sib,siblings⟩
      step with recover_left idx v sib as ⟨l,left⟩
      step with recover_right idx sib v as ⟨r,right⟩
      step with recover_parents N idx as ⟨parents,indices⟩
      step with recover_parent_addresses N a it.start (by have h : p.a.val ≤ 14 := hp.valid.a_le;omega) parents as ⟨addresses,rows⟩
      step with pair_fips seed addresses l r perms hp.le32 (aligned_hash hp) as ⟨out,hash⟩
      refine ⟨hen.trans he,by omega,?_,by omega⟩
      intro j hj
      rw [hn,indices j hj]
      have pair : bytes out.val[j]!.val = Spec.H (Shake.params p) (bytes seed.val)
          {adrsS a with word2:=it.start.val+1,word3:=idx.val[j]!.val/2}
          (pairMsg (bytes v.val[j]!.val)
            (Spec.block (Shake.params p) (bytes sig.val) (trees.val[j]!.val*(p.a.val+1)+1+it.start.val)) idx.val[j]!.val) := by
        rw [hash j hj,rows j hj,indices j hj,left j hj,right j hj]
        by_cases even : idx.val[j]!.val%2=0 <;>
          simp only [pairMsg,even,↓reduceIte,siblings j hj] <;>
          simp only [Spec.H,Shake.params,paramsS_n,hp.n_eq,List.append_assoc]
      rw [pair]
      exact climb_step _ _ _ _ _ _ _ _ _ lt (prior j hj)
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=p.a.val := by rw [he] at more;omega
      intro j hj
      rw [forsRoot_eq]
      have final := (prior j hj).1
      rw [eq] at final
      exact final
  · exact ⟨rfl,Nat.zero_le _,start⟩

end slhdsa.ShakeBatch
