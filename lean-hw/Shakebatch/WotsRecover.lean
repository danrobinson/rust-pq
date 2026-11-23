import Shakebatch.WotsSign
import Shakebatch.RecoverStream
import Shakebatch.WotsKeys
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [ok : StreamCorrect]

theorem recover_absorb {N : Usize} (s : Slice (Array U8 N)) (pk : stream.State)
    (initial : Spec.Bytes) (root : Nat → Spec.Bytes) (prior : ok.Absorbed pk initial)
    (rows : ∀ j < s.length, bytes s.val[j]!.val=root j) :
    shake.batch.recover_loop1 ⟨s,0⟩ pk ⦃ out => ok.Absorbed out (initial ++ (List.range s.length).flatMap root) ⦄ := by
  change shake.fors_batch.recover_loop0_loop1 ⟨s,0⟩ pk ⦃ out => ok.Absorbed out (initial ++ (List.range s.length).flatMap root) ⦄
  simpa only [Nat.zero_add] using absorb_roots s pk initial 0 root (by simpa using prior) (by simpa using rows)

theorem recover_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (seed : Array U8 N) (a : address.Adrs) (digits : Slice U32)
    (positive : 0<machine.width.val) (permutes : PermutationCorrect) (count : digits.length≤67)
    (valid : ∀ i < digits.length, digits.val[i]!.val<16) (size : digits.length*N.val≤sig.length) :
    shake.batch.recover sig seed a digits ⦃ out => bytes out.val=Spec.shake256
      ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS a)).bytes) ++ (List.range digits.length).flatMap
        (recoveredChain p sig seed a digits.val)) N.val ⦄ := by
  unfold shake.batch.recover
  step with WotsOrder.order_spec digits count valid as ⟨order,packed⟩
  step as ⟨s,content,len⟩
  simp only [Slice.len_val] at *
  have ids := sorted_slice digits count order packed s (by simpa using content) len
  simp only [core.slice.Slice.chunks,show machine.width.val≠0 by omega,ite_false,bind_ok]
  step with recover_batches p hp sig seed a digits s positive permutes count len ids size
    (by intro i hi;have := valid i hi;omega) _ as ⟨endpoints,done⟩
  step as ⟨typed,_,fields⟩
  step as ⟨pk,domain⟩
  step with ok.start seed pk as ⟨init,prior⟩
  step as ⟨active,rows,used⟩
  simp only [Slice.len_val] at used rows
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  have found (j : Nat) (hj : j<active.length) : bytes active.val[j]!.val=recoveredChain p sig seed a digits.val j := by
    have hj' : j<digits.length := by omega
    have shape : active.val=endpoints.val.slice 0 digits.length := by simpa using rows
    rw [shape,slice0_getElem! _ _ _ hj' (by simpa using count)]
    exact done j hj' (WotsOrder.rank_lt digits.val j hj')
  step with recover_absorb active init _ _ prior found as ⟨last,absorbed⟩
  rw [used] at absorbed
  rw [← adrsS_pk a typed pk fields domain]
  exact ok.digest N last _ absorbed

#print axioms recover_spec
end slhdsa.ShakeBatch
