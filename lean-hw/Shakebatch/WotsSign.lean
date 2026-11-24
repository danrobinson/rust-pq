import Shakebatch.WotsBatches
import Shakebatch.WotsScatter
import Spec.Correctness
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 700000
variable [machine : Machine]

theorem sorted_slice (digits : Slice U32) (count : digits.length≤67) (order : Array Usize 67#usize)
    (packed : ∀ i < digits.length, order.val[WotsOrder.rank digits.val i]!.val=i)
    (s : Slice Usize) (content : s.val=order.val.slice 0 digits.length) (size : s.length=digits.length) :
    BatchMatches digits.val s 0 := by
  intro j hj
  rw [content,slice0_getElem! _ _ _ (by omega) (by simpa using count),Nat.zero_add]
  exact WotsOrder.order_at order packed j (show j < digits.length by omega)

theorem signed_bytes {ds : List U32} {n : Nat} {root : Nat → Spec.Bytes} (sig : alloc.vec.Vec U8)
    (rows : SignedPrefix ds n root ds.length sig) (width : ∀ j, (root j).length=n) :
    bytes sig.val=(List.range ds.length).flatMap root := by
  have blocks (k : Nat) (inside : k≤ds.length) :
      (bytes sig.val).take (k*n)=(List.range k).flatMap root := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : k < ds.length := inside
      rw [Nat.succ_mul,List.take_add,ih (by omega),List.range_succ,List.flatMap_append,List.flatMap_singleton]
      congr 1
      apply List.ext_getElem
      · have bound := Nat.mul_le_mul_right n inside
        have size := rows.1
        simp only [List.length_take,List.length_drop,bytes_length,width]
        change min n (sig.length-k*n)=n
        rw [Nat.succ_mul] at bound
        omega
      · intro j hj hj'
        have inBlock : j<n := by simpa [width] using hj'
        have inSig : k*n+j<sig.length := by
          have bound := Nat.mul_le_mul_right n inside
          rw [Nat.succ_mul] at bound
          have := rows.1;omega
        rw [List.getElem_take,List.getElem_drop,← getElem!_pos,bytes_getElem!,← getElem!_pos,← getElem!_pos]
        exact rows.2 k hk (WotsOrder.rank_lt ds k hk) j inBlock
        exact inSig
  have eq := blocks ds.length (by omega)
  have size : (bytes sig.val).length=ds.length*n := (bytes_length _).trans rows.1
  simpa only [← size,List.take_length] using eq

theorem sign_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (digits : Slice U32)
    (positive : 0<machine.width.val) (permutes : PermutationCorrect)
    (count : digits.length≤67) (valid : ∀ i < digits.length, digits.val[i]!.val<16) :
    shake.batch.sign sk seed a digits ⦃ out =>
      bytes out.val=(List.range digits.length).flatMap (signedChain p sk seed a digits.val) ∧ out.length=digits.length*N.val ⦄ := by
  unfold shake.batch.sign
  step with WotsOrder.order_spec digits count valid as ⟨order,packed⟩
  have size := hp.le32
  step as ⟨n,total⟩
  step as ⟨sig,init⟩
  step as ⟨s,content,len⟩
  simp only [Slice.len_val] at *
  have ids := sorted_slice digits count order packed s (by simpa using content) len
  simp only [core.slice.Slice.chunks,show machine.width.val≠0 by omega,ite_false,bind_ok]
  step with sign_batches p hp sk seed a digits s positive permutes count len ids sig (by simpa [List.length_replicate,total,Nat.mul_comm] using congrArg List.length init) as ⟨out,done⟩
  refine ⟨signed_bytes out done ?_,done.1⟩
  intro j
  unfold signedChain
  cases digit : (digits.val[j]!).val with
  | zero => simp [Spec.chain,Spec.PRF,Shake.params,hp.n_eq]
  | succ n => rw [chain_succ];simp [Spec.F,Shake.params,hp.n_eq]

#print axioms sign_spec
end slhdsa.ShakeBatch
