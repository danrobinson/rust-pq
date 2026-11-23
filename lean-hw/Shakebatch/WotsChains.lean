import Shakebatch.WotsLoop
import Shakebatch.WotsDecode
import Shakebatch.WotsSecrets
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 600000
variable [machine : Machine]

theorem wots_chains {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (seed : Array U8 N) (addr : address.Adrs) (ids : Array Usize machine.width)
    (values : Array (Array U8 N) machine.width) (first last : Array U32 machine.width)
    (fits : ∀ j < machine.width.val, ids.val[j]!.val < 2^32)
    (order : ∀ j < machine.width.val, first.val[j]!.val ≤ last.val[j]!.val)
    (permutes : PermutationCorrect) :
    shake.batch.chains seed addr ids values first last ⦃ out => ∀ j < machine.width.val,
      bytes out.val[j]!.val = Spec.chain (Shake.params p) (bytes values.val[j]!.val) first.val[j]!.val
        (last.val[j]!.val-first.val[j]!.val) (bytes seed.val) {(adrsS addr) with word2:=ids.val[j]!.val} ⦄ := by
  let base := fun j : Nat => {addr with word2:=UScalar.cast .U32 ids.val[j]!}
  let inst := shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N
  let post := fun (j : Nat) (v : address.Adrs) => v={base j with word3:=0#u32}
  have each (i : Usize) (hi : i.val < machine.width.val) :
      inst.call_mut (addr,ids) i ⦃ x g => post i.val x ∧ g=(addr,ids) ⦄ := by
    change shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut (N:=N) (addr,ids) i ⦃ _ ⦄
    unfold shake.batch.chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
    step as ⟨v,get⟩
    rw [get,← getElem!_pos]
    simp [base,post,address.Adrs.with_word2,address.Adrs.with_word3,lift,bind_ok,step_simps]
    rfl
  unfold shake.batch.chains
  step with core.array.from_fn.spec_stateless_getElem! machine.width inst (addr,ids) post each as ⟨addresses,rows⟩
  have bound := hp.le32
  have aligned := aligned_hash hp
  step as ⟨n2,twice⟩
  step as ⟨size,sz⟩
  step with header_spec seed addresses size bound (by omega) as ⟨header,head⟩
  step as ⟨count,nc⟩
  step as ⟨offset,off⟩
  step with put_spec header offset values (by omega) as ⟨st,writes⟩
  have init : chainInv p seed base values first last first st := by
    intro j hj
    refine ⟨Nat.le_refl _,order j hj,values.val[j]!,by simp [Spec.chain],?_⟩
    intro k hk
    have row := rows j hj
    change addresses[j]! = {base j with word3:=0#u32} at row
    rw [Array.getElem!_Nat_eq] at row
    rw [writes k hk j hj,head k hk j hj,row]
    simp only [payloadLayout,off,nc,sz,twice,Array.getElem!_Nat_eq]
  step with chain_loop p hp seed base values count offset nc (by omega) first last st init permutes (aligned_hash hp) as ⟨st',done⟩
  step with chain_result count offset st' _ nc (by omega) (aligned_hash hp) as ⟨out,written⟩
  rename_i j hj
  obtain ⟨_,_,v,chain,fields⟩ := done j hj
  have same : out.val[j]!.val = v.val := by
    apply List.ext_getElem
    · simp
    · intro b hl hr
      have size : b<N.val := by simpa using hr
      have payload : cell st' (offset.val+b/8) j = inputWord v.val (b/8) := by
        rw [fields _ (by omega)]
        simp only [payloadLayout]
        rw [if_pos (by omega)]
        congr 1
        omega
      have eq := decoded_cell st' j offset.val b v size (aligned_hash hp) payload
      rw [← written j hj b size] at eq
      apply UScalar.eq_of_val_eq
      apply congrArg BitVec.toNat
      simpa only [outputByte,getElem!_pos out.val[j]!.val b hl,getElem!_pos v.val b hr] using eq
  rw [same,chain]
  have cast := Nat.mod_eq_of_lt (fits j hj)
  simp only [base,adrsS,UScalar.cast_val_eq,UScalarTy.U32_numBits_eq,cast]

#print axioms wots_chains

end slhdsa.ShakeBatch
