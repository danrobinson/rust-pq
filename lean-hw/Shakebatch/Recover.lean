import Shakebatch.RecoverRoots
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [ok : StreamCorrect]

/-- Algorithm 17 for arbitrary valid FORS message indices and any signature of the required size. -/
theorem recover_fors_trees {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig : Slice U8)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (seed : Array U8 N) (a : address.Adrs)
    (perms : PermutationCorrect) (enabled : 0 < machine.width.val)
    (choices : Slice U32) (count : choices.length=p.k.val)
    (index : ∀ j < choices.length, choices.val[j]!.val < 2^p.a.val) :
    shake.fors_batch.recover p choices sig seed a ⦃ out => bytes out.val =
      Spec.T (Shake.params p) (bytes seed.val)
        {(adrsS a).setTypeAndClear Spec.FORS_ROOTS with keypair := (adrsS a).keypair}
        ((List.range p.k.val).flatMap (forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val)
          (adrsS a) (nats choices.val))) ⦄ := by
  have ha : p.a.val ≤ 14 := hp.valid.a_le
  unfold shake.fors_batch.recover
  simp only [lift,bind_ok]
  step as ⟨stride,st⟩
  have str : stride.val=p.a.val+1 := by simp [st]
  step as ⟨addr,_,adr⟩
  step as ⟨addr1,adr1⟩
  step with ok.start seed addr1 as ⟨s,st0⟩
  step as ⟨iter,init,width⟩
  step with recover_roots p hp sig len seed a perms enabled choices count index stride str s _ st0 iter width init
    as ⟨final,h⟩
  let* ⟨out,hashed⟩ ← ok.digest N final _ h
  have key : adrsS addr1={(adrsS a).setTypeAndClear Spec.FORS_ROOTS with keypair:=(adrsS a).keypair} := by
    simp [adr1,adr,adrsS,Spec.Adrs.setTypeAndClear,Spec.FORS_ROOTS,address.FORS_ROOTS]
  simpa only [Spec.T,Shake.params,paramsS_n,hp.n_eq,key] using hashed

end slhdsa.ShakeBatch
