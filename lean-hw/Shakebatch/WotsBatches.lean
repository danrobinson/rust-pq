import Shakebatch.WotsChunkFold
import Shakebatch.WotsChains
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 700000
variable [machine : Machine]

def signedChain {N : Usize} (p : slhdsa.params.Params) (sk seed : Array U8 N) (addr : address.Adrs) (ds : List U32) (j : Nat) :=
  Spec.chain (Shake.params p)
    (Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val) {Spec.wotsSkAdrs (adrsS addr) with word2:=j})
    0 ds[j]!.val (bytes seed.val) {adrsS addr with word2:=j}

def recoveredChain {N : Usize} (p : slhdsa.params.Params) (sig : Slice U8) (seed : Array U8 N) (addr : address.Adrs) (ds : List U32) (j : Nat) :=
  Spec.chain (Shake.params p) (bytes ((sig.val.drop (j*N.val)).take N.val)) ds[j]!.val (15-ds[j]!.val)
    (bytes seed.val) {adrsS addr with word2:=j}

theorem sign_batches {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (digits : Slice U32)
    (order : Slice Usize) (positive : 0<machine.width.val) (permutes : PermutationCorrect)
    (count : digits.length≤67) (length : order.length=digits.length) (orderOk : BatchMatches digits.val order 0)
    (sig : alloc.vec.Vec U8) (prior : sig.length=digits.length*N.val) :
    shake.batch.sign_loop0 ⟨order,machine.width⟩ sk seed addr digits sig ⦃ out =>
      SignedPrefix digits.val N.val (signedChain p sk seed addr digits.val) digits.length out ⦄ := by
  unfold shake.batch.sign_loop0
  apply chunk_fold (shake.batch.sign_loop0.body sk seed addr digits) digits.val order machine.width positive length orderOk
    (SignedPrefix digits.val N.val (signedChain p sk seed addr digits.val)) sig
    (by exact ⟨prior,fun _ _ h => by omega⟩)
  · intro it s stop _;unfold nextChunk at stop;simp only [shake.batch.sign_loop0.body,stop,bind_ok];rfl
  · intro offset it nxt slice s prior ids nonempty width run
    unfold shake.batch.sign_loop0.body
    unfold nextChunk at run
    simp only [run,bind_ok]
    step with batch_ids (N:=N) slice nonempty as ⟨lanes,indices⟩
    have inRange (j : Nat) (hj : j<machine.width.val) : lanes.val[j]!.val<digits.length := by
      rw [indices j hj]
      exact (ids _ (by omega)).1
    have fits (j : Nat) (hj : j<machine.width.val) : lanes.val[j]!.val<2^32 := by have := inRange j hj;omega
    step with wots_secrets p hp seed sk addr lanes fits permutes as ⟨secrets,prf⟩
    step with limit_digits (N:=N) digits lanes inRange as ⟨stops,ends⟩
    let first := Array.repeat machine.width 0#u32
    have zero (j : Nat) (hj : j<machine.width.val) : first.val[j]!.val=0 := by simp [first,hj]
    step with wots_chains p hp seed addr lanes secrets first stops fits (fun j hj => by rw [zero j hj];omega) permutes as ⟨vals,chained⟩
    have good (j : Nat) (hj : j<slice.length) : bytes vals.val[j]!.val=signedChain p sk seed addr digits.val slice.val[j]!.val := by
      have bound : j<machine.width.val := by omega
      rw [chained j bound,prf j bound,zero j bound,ends j bound,indices j bound,Nat.min_eq_left (by omega)]
      simp [signedChain]
    simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
    step with store_signatures digits.val _ offset slice count hp.le32 width ids vals good s prior as ⟨out,done⟩
    exact ⟨out,rfl,done⟩

theorem recover_batches {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (seed : Array U8 N) (addr : address.Adrs) (digits : Slice U32)
    (order : Slice Usize) (positive : 0<machine.width.val) (permutes : PermutationCorrect)
    (count : digits.length≤67) (length : order.length=digits.length) (orderOk : BatchMatches digits.val order 0)
    (size : digits.length*N.val ≤ sig.length) (valid : ∀ i<digits.length, digits.val[i]!.val≤15)
    (initial : Array (Array U8 N) 67#usize) :
    shake.batch.recover_loop0 ⟨order,machine.width⟩ sig seed addr digits initial ⦃ out =>
      EndpointPrefix digits.val (recoveredChain p sig seed addr digits.val) digits.length out ⦄ := by
  unfold shake.batch.recover_loop0
  apply chunk_fold (shake.batch.recover_loop0.body sig seed addr digits) digits.val order machine.width positive length orderOk
    (EndpointPrefix digits.val (recoveredChain p sig seed addr digits.val)) initial (fun _ _ h => by omega)
  · intro it s stop _;unfold nextChunk at stop;simp only [shake.batch.recover_loop0.body,stop,bind_ok];rfl
  · intro offset it nxt slice s prior ids nonempty width run
    unfold shake.batch.recover_loop0.body
    unfold nextChunk at run
    simp only [run,bind_ok]
    have idsProof : core.array.from_fn machine.width (shake.batch.recover.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N) slice ⦃ out => ∀ j < machine.width.val, out.val[j]! = slice.val[min j (slice.length-1)]! ⦄ := batch_ids (N:=N) slice nonempty
    step with idsProof as ⟨lanes,indices⟩
    have inRange (j : Nat) (hj : j<machine.width.val) : lanes.val[j]!.val<digits.length := by
      rw [indices j hj];exact (ids _ (by omega)).1
    have fits (j : Nat) (hj : j<machine.width.val) : lanes.val[j]!.val<2^32 := by have := inRange j hj;omega
    step with recover_blocks (N:=N) sig lanes (fun j hj => (Nat.mul_le_mul_right _ (inRange j hj)).trans size) as ⟨vs,blocks⟩
    have digitsProof : core.array.Array.map (shake.batch.recover.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) lanes digits ⦃ out => ∀ j < machine.width.val, out.val[j]! = digits.val[lanes.val[j]!.val]! ⦄ := limit_digits (N:=N) digits lanes inRange
    step with digitsProof as ⟨starts,lower⟩
    simp only [W_eq]
    step as ⟨endStep,endVal⟩
    let last := Array.repeat machine.width endStep
    have finish (j : Nat) (hj : j<machine.width.val) : last.val[j]!.val=15 := by simpa [last,hj] using endVal
    step with wots_chains p hp seed addr lanes vs starts last fits
      (fun j hj => by rw [lower j hj,finish j hj];exact valid _ (inRange j hj)) permutes as ⟨vals,chained⟩
    have good (j : Nat) (hj : j<slice.length) : bytes vals.val[j]!.val=recoveredChain p sig seed addr digits.val slice.val[j]!.val := by
      have bound : j<machine.width.val := by omega
      rw [chained j bound,blocks j bound,finish j bound,lower j bound,indices j bound,Nat.min_eq_left (by omega)]
      rfl
    simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default,bind_ok]
    step with store_endpoints digits.val _ offset slice count width ids vals good s prior as ⟨out,done⟩
    exact ⟨out,rfl,done⟩

end slhdsa.ShakeBatch
