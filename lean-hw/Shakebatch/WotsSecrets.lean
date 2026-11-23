import Shakebatch.WotsChainProgram
import Shakebatch.ForsSecrets
import Slhdsa.Proofs.ShakeWots
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem wots_secrets {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (seed sk : Array U8 N) (addr : address.Adrs) (ids : Array Usize machine.width)
    (fits : ∀ j < machine.width.val, ids.val[j]!.val < 2^32)
    (permutes : PermutationCorrect) :
    shake.batch.secrets seed sk addr ids ⦃ out => ∀ j < machine.width.val, bytes out.val[j]!.val =
      Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val)
        { Spec.wotsSkAdrs (adrsS addr) with word2 := ids.val[j]!.val } ⦄ := by
  unfold shake.batch.secrets
  step as ⟨a,atype,fields⟩
  step as ⟨prf,key⟩
  let inst := shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N
  let post := fun (j : Nat) (v : address.Adrs) =>
    ∃ (word : U32), word.val=ids.val[j]!.val ∧ v={prf with word2:=word}
  have each (i : Usize) (hi : i.val < machine.width.val) :
      inst.call_mut (prf,ids) i ⦃ x g => post i.val x ∧ g=(prf,ids) ⦄ := by
    change shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut (N:=N) (prf,ids) i ⦃ _ ⦄
    unfold shake.batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
    step as ⟨v,get⟩
    simp only [lift,bind_ok,address.Adrs.with_word2,step_simps]
    refine ⟨⟨_,?_,rfl⟩,rfl⟩
    rw [UScalar.cast_val_eq,get,← getElem!_pos]
    exact Nat.mod_eq_of_lt (fits i.val hi)
  step with core.array.from_fn.spec_stateless_getElem! machine.width inst (prf,ids) post each as ⟨addresses,rows⟩
  step with short_fips seed addresses (Array.repeat machine.width sk) permutes hp.le32 (aligned_hash hp) as ⟨out,hash⟩
  rename_i j hj
  obtain ⟨word,hw,row⟩ := rows j hj
  rw [hash j hj,← Array.getElem!_Nat_eq,row,Array.repeat_val]
  simp [key,fields,hw,Spec.wotsSkAdrs,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,adrsS,
    Spec.Adrs.setTypeAndClear,address.WOTS_PRF,Spec.WOTS_PRF,List.append_assoc,hj]

end slhdsa.ShakeBatch
