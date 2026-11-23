import Shakebatch.WotsLayout
import Shakebatch.WotsWords
import Shakebatch.WotsProgress
import Slhdsa.Proofs.ShakeWots
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 800000
variable [machine : Machine]

private theorem one_step {N : Usize} (seed : Array U8 N) (a : address.Adrs) (val : Array U8 N)
    (ix : U32) (out tagged : Matrix machine.width) (j : Nat) (hj : j < machine.width.val)
    (small : N.val ≤ 32) (align : N.val%8=0)
    (perm : lane out j=Spec.Keccak.permute (lane tagged j))
    (cells : ∀ k < 25, cell tagged k j =
      if k=N.val/8+4-1 then payloadLayout seed {a with word3:=0#u32} val k ||| wordTag ix
      else payloadLayout seed {a with word3:=0#u32} val k) :
    Spec.Keccak.squeeze (lane out j) 0 N.val =
      Spec.shake256 (bytes seed.val ++ ((adrsS {a with word3:=ix}).bytes ++ bytes val.val)) N.val := by
  rw [perm,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun s => Spec.Keccak.squeeze (Spec.Keccak.permute s) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,cells k hk]
  exact tagged_layout seed a val ix small align k

def chainInv {N : Usize} (p : slhdsa.params.Params) (seed : Array U8 N)
    (base : Nat → address.Adrs) (startVals : Array (Array U8 N) machine.width)
    (first last ix : Array U32 machine.width) (s : Matrix machine.width) :=
  ∀ j < machine.width.val, first.val[j]!.val ≤ ix.val[j]!.val ∧ ix.val[j]!.val ≤ last.val[j]!.val ∧
    ∃ v : Array U8 N, bytes v.val = Spec.chain (Shake.params p) (bytes startVals.val[j]!.val)
        first.val[j]!.val (ix.val[j]!.val-first.val[j]!.val) (bytes seed.val) (adrsS (base j)) ∧
      ∀ k < 25, cell s k j = payloadLayout seed {base j with word3:=0#u32} v k

theorem chain_loop {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (seed : Array U8 N) (base : Nat → address.Adrs) (startVals : Array (Array U8 N) machine.width)
    (count offset : Usize) (nc : count.val=N.val/8) (off : offset.val=N.val/8+4)
    (first last : Array U32 machine.width) (s : Matrix machine.width)
    (init : chainInv p seed base startVals first last first s) (permutes : PermutationCorrect)
    (align : N.val%8=0) :
    shake.batch.chains_loop0 count first last s offset ⦃ out => chainInv p seed base startVals first last last out ⦄ := by
  unfold shake.batch.chains_loop0
  apply loop.spec_decr_nat (measure := fun q : Array U32 machine.width × Matrix machine.width => remaining q.1 last)
    (inv := fun q => chainInv p seed base startVals first last q.1 q.2)
  · rintro ⟨ix,state⟩ inv
    change chainInv p seed base startVals first last ix state at inv
    unfold shake.batch.chains_loop0.body
    step with unequal_spec ix last as ⟨b,ne⟩
    cases b with
    | false =>
      have eq : ix=last := by simpa using ne
      simpa only [Bool.false_eq_true,ite_false,step_simps,← eq] using inv
    | true =>
      have different : ix≠last := ne.mp rfl
      simp only [ite_true]
      have bound := hp.le32
      step with chain_tag state offset ix (by omega) (by omega) as ⟨tagged,attached⟩
      step with permutes tagged as ⟨out,hashed⟩
      obtain ⟨digests,byLane,words⟩ := digest_words (N:=N) out (by omega) align
      step with advance_lanes count offset state out ix last (by omega) as ⟨next,s',moved,copied⟩
      constructor
      · intro j hj
        obtain ⟨lo,hi,prior,chain,fields⟩ := inv j hj
        have stepIx := moved j hj
        by_cases live : ix.val[j]!.val < last.val[j]!.val
        · rw [if_pos live] at stepIx
          refine ⟨by omega,by omega,digests.val[j]!,?_,?_⟩
          · have word := one_step seed (base j) prior ix.val[j]! out tagged j hj bound align (hashed j hj)
              (fun k hk => by rw [attached k hk j hj,fields k hk,off])
            rw [byLane j hj,word,stepIx,show ix.val[j]!.val+1-first.val[j]!.val=(ix.val[j]!.val-first.val[j]!.val)+1 by omega,
              chain_succ,show first.val[j]!.val+(ix.val[j]!.val-first.val[j]!.val)=ix.val[j]!.val by omega,← chain]
            simp [Spec.F,Shake.params,paramsS_n,hp.n_eq,adrsS]
          · intro k hk
            rw [copied k hk j hj,fields k hk,off,nc]
            unfold payloadLayout
            simp only [live,true_and]
            by_cases pos : N.val/8+4 ≤ k ∧ k<N.val/8+4+N.val/8
            · simp only [pos,ite_true]
              exact (words j hj _ (by omega)).symm
            · simp only [pos,ite_false]
        · rw [if_neg live,Nat.add_zero] at stepIx
          refine ⟨by omega,by omega,prior,?_,?_⟩
          · simpa only [stepIx] using chain
          · intro k hk
            simpa only [copied k hk j hj,live,false_and,ite_false] using fields k hk
      · exact remaining_decreases ix next last different (fun j hj => (inv j hj).2.1) moved
  · exact init

end slhdsa.ShakeBatch
