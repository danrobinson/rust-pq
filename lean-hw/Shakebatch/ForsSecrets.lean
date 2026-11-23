import Shakebatch.Pair
import Shakebatch.Map
import Slhdsa.Proofs.ShakeFors
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

omit machine in
theorem aligned_hash {N : Usize} {p : slhdsa.params.Params} (hp : PN p N) : N.val%8=0 := by
  rcases hp.nok with h|h|h <;> omega

theorem fors_secrets {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (indices : Array U32 machine.width)
    (permutes : PermutationCorrect) :
    shake.fors_batch.secrets sk seed addr indices ⦃ out =>
      ∀ j < machine.width.val, bytes out.val[j]!.val =
        Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS addr) indices.val[j]!.val ⦄ := by
  unfold shake.fors_batch.secrets
  step as ⟨a,atype,fields⟩
  step as ⟨prf,key⟩
  let inst := shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs N
  let post := fun (j : Nat) (v : address.Adrs) => v = {prf with word3:=indices.val[j]!}
  have each (j : Nat) (_ : j < machine.width.val) :
      inst.call_mut prf indices.val[j]! ⦃ x g => post j x ∧ g=prf ⦄ := by
    simp [inst,post,shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs,
      shake.fors_batch.secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut,
      address.Adrs.with_word3,step_simps]
  step with map_spec inst indices prf post each as ⟨addresses,rows⟩
  step with short_fips seed addresses (Array.repeat machine.width sk) permutes hp.le32 (aligned_hash hp) as ⟨out,hash⟩
  rename_i j hj
  have same := rows j hj
  rw [hash j hj,same,Array.repeat_val]
  simp only [key,fields,Spec.forsSkGen,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,adrsS,
    Spec.Adrs.setTypeAndClear,Spec.FORS_PRF,fors_FORS_PRF_eq,List.append_assoc]
  simp [hj]
end slhdsa.ShakeBatch
