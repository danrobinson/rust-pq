import Shakebatch.WotsKeyProgram
import Shakebatch.WotsChains
import Shakebatch.RecoverStream
import Parent256.Driver
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 800000
variable [machine : Machine] [stream : Stream] [ok : StreamCorrect]

theorem key_absorb {N : Usize} (slice : Slice (Array U8 N)) (pk : stream.State)
    (initialBytes : Spec.Bytes) (first : Nat) (root : Nat → Spec.Bytes)
    (prior : ok.Absorbed pk (initialBytes ++ (List.range first).flatMap root))
    (values : ∀ j < slice.length, bytes slice.val[j]!.val=root (first+j)) :
    shake.batch.keygen_loop0_loop0 ⟨slice,0⟩ pk ⦃ out =>
      ok.Absorbed out (initialBytes ++ (List.range (first+slice.length)).flatMap root) ⦄ := by
  exact absorb_roots slice pk initialBytes first root prior values

theorem key_batches {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (len : Usize) (length : len.val=2*N.val+3)
    (init : stream.State) (domain : Spec.Bytes) (prior : ok.Absorbed init domain)
    (positive : 0 < machine.width.val) (width : machine.width.val ≤ 8) (permutes : PermutationCorrect) :
    shake.batch.keygen_loop0 ⟨⟨0#usize,len⟩,machine.width⟩ sk seed addr.layer addr.tree addr.typ addr.keypair addr.word2 addr.word3 len init ⦃ out =>
      ok.Absorbed out (domain ++ (List.range len.val).flatMap
        (pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS addr))) ⦄ := by
  let root := pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS addr)
  have small := hp.le32
  unfold shake.batch.keygen_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize) × stream.State => len.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end=len ∧ q.1.step_by=machine.width ∧
      ok.Absorbed q.2 (domain ++ (List.range (min q.1.iter.start.val len.val)).flatMap root))
  · rintro ⟨it,s⟩ ⟨stop,stride,old⟩
    simp only at stop stride old
    unfold shake.batch.keygen_loop0.body
    by_cases live : it.iter.start.val < it.iter.end.val
    · have valid : it.iter.start.val < len.val := stop ▸ live
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it (stride ▸ positive) as ⟨o,nxt,info,he,hw⟩
      simp only [live,ite_true] at info
      obtain ⟨ho,hn⟩ := info
      simp only [ho,bind_ok]
      let inst := shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N
      let pos := it.iter.start
      let byId := fun (j : Nat) (v : Usize) => v.val=pos.val+j
      have each (i : Usize) (hi : i.val < machine.width.val) :
          inst.call_mut pos i ⦃ x g => byId i.val x ∧ g=pos ⦄ := by
        change shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut (N:=N) pos i ⦃ _ ⦄
        unfold shake.batch.keygen.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
        have hpos : pos.val < len.val := valid
        step as ⟨v,eq⟩
        exact eq
      step with core.array.from_fn.spec_stateless_getElem! machine.width inst pos byId each as ⟨ids,idspec⟩
      have indices (j : Nat) (hj : j < machine.width.val) : ids.val[j]!.val=it.iter.start.val+j := by
        simpa only [Array.getElem!_Nat_eq,byId,pos] using idspec j hj
      have fits (j : Nat) (hj : j<machine.width.val) : ids.val[j]!.val < 2^32 := by rw [indices j hj];omega
      step with wots_secrets p hp seed sk addr ids fits permutes as ⟨secret,prf⟩
      simp only [W_eq]
      step as ⟨endStep,endVal⟩
      let first := Array.repeat machine.width 0#u32
      let last := Array.repeat machine.width endStep
      have starts (j : Nat) (hj : j<machine.width.val) : first.val[j]!.val=0 := by simp [first,hj]
      have stops (j : Nat) (hj : j<machine.width.val) : last.val[j]!.val=15 := by simpa [last,hj] using endVal
      step with wots_chains p hp seed addr ids secret first last fits (fun j hj => by rw [starts j hj,stops j hj];decide) permutes as ⟨ends,done⟩
      have endpoint (j : Nat) (hj : j<machine.width.val) : bytes ends.val[j]!.val=root (pos.val+j) := by
        rw [done j hj,prf j hj,starts j hj,stops j hj,indices j hj]
        rfl
      step as ⟨left,sub⟩
      simp only [lift,bind_ok]
      step as ⟨slice,take,taken⟩
      simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
      have count : slice.length=min (len.val-pos.val) machine.width.val := by
        rw [taken]
        change (if machine.width.val < left.val then machine.width else left).val=_
        split <;> rename_i h
        · rw [min_eq_right (by dsimp [pos];omega)]
        · rw [min_eq_left (by dsimp [pos];omega),sub]
      have rows (j : Nat) (hj : j<slice.length) : bytes slice.val[j]!.val=root (pos.val+j) := by
        have smallj : j<machine.width.val := by omega
        rw [take]
        have lim : j<min left.val machine.width.val := by rw [sub];exact count ▸ hj
        simp only [List.slice,List.drop_zero,Array.val_to_slice]
        rw [List.getElem!_take_of_lt _ j _ (by simpa [taken] using hj)]
        exact endpoint j smallj
      step with key_absorb slice s domain pos.val root (by simpa [min_eq_left (Nat.le_of_lt valid),pos] using old) rows as ⟨next,added⟩
      have advance : nxt.iter.start.val=min (pos.val+machine.width.val) len.val := by rw [hn,stride,stop]
      refine ⟨he.trans stop,hw.trans stride,?_,by dsimp [pos] at advance;omega⟩
      simpa only [show min nxt.iter.start.val len.val=pos.val+slice.length by dsimp [pos] at *;omega] using added
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      simpa [min_eq_right (show len.val ≤ it.iter.start.val by rw [stop] at live;omega),root] using old
  · simpa using prior

theorem keygen_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (positive : 0 < machine.width.val) (width : machine.width.val ≤ 8) (permutes : PermutationCorrect) :
    shake.batch.keygen sk seed a ⦃ out => bytes out.val = Spec.wotsPkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) ⦄ := by
  unfold shake.batch.keygen
  have bound := hp.le32
  simp only [LEN2_eq]
  step as ⟨twice,n2⟩
  step as ⟨len,length⟩
  step as ⟨typed,_,fields⟩
  step as ⟨pk,domain⟩
  step with ok.start seed pk as ⟨init,prior⟩
  step as ⟨iter,generated,stride⟩
  have iterEq : iter=⟨⟨0#usize,len⟩,machine.width⟩ := by cases iter; congr
  rw [iterEq]
  step with key_batches p hp sk seed a len (by omega) init _ prior positive width permutes as ⟨s,done⟩
  have result := ok.digest N s _ done
  have plen : (Shake.params p).len=len.val := by change (paramsS p).len=_;rw [hp.len];omega
  have pn : (Shake.params p).n=N.val := hp.n
  have addr := adrsS_pk a typed pk fields domain
  change stream.digest N s ⦃ out => bytes out.val=Spec.shake256
    ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS a)).bytes) ++ (List.range (Shake.params p).len).flatMap
      (pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a))) (Shake.params p).n ⦄
  rw [plen,pn,← addr]
  exact result

#print axioms keygen_spec
end slhdsa.ShakeBatch
