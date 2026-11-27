import Cachepath.NativeVerify.ForsRoots
import Shakebatch.ForsDispatch

open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1600000
variable [machine : Machine] [accelerator : ActiveKernel machine] [stream : Stream] [ok : StreamCorrect]

def Domain (a : address.Adrs) := a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32

theorem native_recovery {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (seed : Array U8 N) (a : address.Adrs)
    (domain : Domain a) (permutes : ActiveCorrect machine accelerator.run) (enabled : 0<machine.width.val)
    (choices : Slice U32) (count : choices.length=p.k.val)
    (index : ∀ j<choices.length, choices.val[j]!.val < 2^p.a.val) :
    recover p choices sig seed a ⦃ out => bytes out.val =
      Spec.T (Shake.params p) (bytes seed.val)
        {(adrsS a).setTypeAndClear Spec.FORS_ROOTS with keypair := (adrsS a).keypair}
        ((List.range p.k.val).flatMap (forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val)
          (adrsS a) (nats choices.val))) ⦄ := by
  have small := hp.le32
  have hgt : p.a.val≤14 := hp.valid.a_le
  unfold recover
  step as ⟨n,nv⟩
  step as ⟨offset,off⟩
  step as ⟨short,shortv⟩
  step as ⟨twice,tv⟩
  step as ⟨pair,pv⟩
  simp only [lift,bind_ok]
  step as ⟨stride,stv⟩
  have str : stride.val=p.a.val+1 := by simp [stv]
  step with seed_spec seed small as ⟨sw,seedWords⟩
  step as ⟨tree,_,treeEq⟩
  step as ⟨tree',treeEq'⟩
  have equal : tree'=a := by
    rcases domain with ⟨typ,w2,w3⟩
    rw [treeEq',treeEq]
    cases a
    simp_all
  step with address_spec tree' as ⟨aw,addressWords⟩
  rw [equal] at addressWords
  step as ⟨roots,_,rootAddr⟩
  step as ⟨roots',finalAddr⟩
  step with ok.start seed roots' as ⟨pk,started⟩
  step as ⟨iter,init,width⟩
  step with all_roots p hp sig len seed a permutes enabled choices count index n offset short pair stride
    str nv off shortv (by omega) sw aw (fun k hk => (seedWords k (by omega)).trans (ite_eq_left (by omega)))
    addressWords pk _ _ started iter width init as ⟨out,absorbed⟩
  let* ⟨value,dig⟩ ← ok.digest N out _ absorbed
  have key : adrsS roots'={(adrsS a).setTypeAndClear Spec.FORS_ROOTS with keypair:=(adrsS a).keypair} := by
    simp [finalAddr,rootAddr,adrsS,Spec.Adrs.setTypeAndClear,Spec.FORS_ROOTS,address.FORS_ROOTS]
  simpa only [Spec.T,Shake.params,paramsS_n,hp.n_eq,key] using dig

def dispatched (available : Usize → Result Bool) {N : Usize} (p : params.Params)
    (sig md : Slice U8) (seed : Array U8 N) (adrs : address.Adrs) : Result (Array U8 N) := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let b ← available N
  if b then recover p (alloc.vec.Vec.deref indices) sig seed adrs
  else
    let a ← address.Adrs.with_type adrs address.FORS_ROOTS
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let roots ← slhdsa.shake.hash.start seed a1
    let roots1 ← slhdsa.shake.fors.fors_pk_from_sig_loop p.a sig seed adrs.layer adrs.tree
      adrs.typ adrs.keypair adrs.word2 adrs.word3 indices roots 0#usize
    slhdsa.shake.hash.digest N roots1

theorem dispatched_fips {N : Usize} (available : Usize → Result Bool) (p : params.Params) (hp : PN p N)
    (sig md : Slice U8) (seed : Array U8 N) (a : address.Adrs) (domain : Domain a)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (hmd : md.length=(p.k.val*p.a.val+7)/8)
    (on : Bool) (select : available N=.ok on)
    (permutes : on=true → ActiveCorrect machine accelerator.run) (width : on=true → 0<machine.width.val) :
    dispatched available p sig md seed a ⦃ out => bytes out.val =
      Spec.forsPkFromSig (Shake.params p) (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄ := by
  cases on with
  | false =>
    convert Shake.fors_pk_from_sig_spec p hp sig md seed a len hmd using 1
    unfold dispatched slhdsa.shake.fors.fors_pk_from_sig
    simp only [select,bind_ok,Bool.false_eq_true,ite_false]
  | true =>
    have ha : p.a.val ≤ 14 := hp.valid.a_le
    have pos : 1 ≤ p.a.val := hp.valid.a_pos
    unfold dispatched
    step as ⟨k,hk⟩
    have kval : k.val=p.k.val := by simp [hk]
    let* ⟨digits,ind,count,valid⟩ ← base_2b_spec md p.a k (by omega) (by rw [kval,hmd];omega)
    rw [kval] at ind count
    have view : digits.deref=digits.slice := by apply Slice.ext; simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    simp only [select,bind_ok,ite_true,view]
    let* ⟨out,bytesEq⟩ ← native_recovery p hp sig len seed a domain (permutes rfl) (width rfl) digits.slice
      count (fun t ht => valid _ (by change digits.val[t]! ∈ digits.val; rw [getElem!_pos digits.val t ht];exact List.getElem_mem _))
    rw [forsPkFromSig_eq,bytesEq]
    change _ = Spec.T _ _ _ ((List.range p.k.val).flatMap (forsRoot _ _ _ _ (Spec.base2b _ p.a.val p.k.val)))
    rw [← ind]
    rfl

end slhdsa.NativeVerify.Fors
