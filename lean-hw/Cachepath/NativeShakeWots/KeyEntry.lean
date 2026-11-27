import Cachepath.NativeShakeWots.Keygen
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1200000
variable [machine : Machine] [accel : Dispatch machine] [stream : Stream] [ok : StreamCorrect]

theorem keygen_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (positive : 0<machine.width.val) (permutes : ActiveCorrect machine accel.permute) :
    keygen sk seed a ⦃ out => bytes out.val = Spec.wotsPkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) ⦄ := by
  unfold keygen
  have small := hp.le32
  simp only [LEN2_eq]
  step as ⟨twice,n2⟩
  step as ⟨len,length⟩
  step with seed_spec seed small as ⟨sw,seedWord⟩
  step with seed_spec sk small as ⟨skw,skWord⟩
  step as ⟨prfT,_,prfTypes⟩
  step as ⟨prf,prfFields⟩
  step with address_spec prf as ⟨ap,apWords⟩
  step as ⟨hashT,_,hashTypes⟩
  step as ⟨hash,hashFields⟩
  step with address_spec hash as ⟨ah,ahWords⟩
  step as ⟨wp,vp⟩
  step as ⟨wh,vh⟩
  step as ⟨pkT,_,pkTypes⟩
  step as ⟨pk,pkFields⟩
  step with ok.start seed pk as ⟨init,prior⟩
  step as ⟨iter,generated,stride⟩
  have iterEq : iter=⟨⟨0#usize,len⟩,machine.width⟩ := by cases iter;congr
  rw [iterEq]
  have rep (w : U64) (l : Nat) (hl : l<machine.width.val) : (Array.repeat machine.width w).val[l]!.bv=w.bv := by
    rw [Array.repeat_val]
    simp [hl]
  rw [← getElem!_pos] at vp vh
  step with key_chunks p hp sk seed prf hash len (by omega) sw skw ap ah (Array.repeat machine.width wp) (Array.repeat machine.width wh) _ init _ prior positive
    (fun i h => by simpa only [ite_eq_left h] using seedWord i (by omega))
    (fun i h => by simpa only [ite_eq_left h] using skWord i (by omega)) apWords ahWords
    (by intro l hl; rw [rep wp l hl,vp];exact apWords 2 (by decide))
    (by intro l hl; rw [rep wh l hl,vh];exact ahWords 2 (by decide))
    permutes as ⟨finalState,done⟩
  have hashEq : hash=a := by
    rw [hashFields,hashTypes]
    obtain ⟨layer,tree,typ,pair,w2,w3⟩ := a
    obtain ⟨t,x,y⟩ := domain
    simp only at t x y
    subst typ;subst w2;subst w3;rfl
  have prfEq : adrsS prf=Spec.wotsSkAdrs (adrsS a) := by
    simp [prfFields,prfTypes,adrsS,Spec.wotsSkAdrs,Spec.Adrs.setTypeAndClear,Spec.WOTS_PRF,WOTS_PRF_eq]
  have plen : (Shake.params p).len=len.val := by change (paramsS p).len=_;rw [hp.len];omega
  have addr := adrsS_pk a pkT pk pkTypes pkFields
  have root (j : Nat) : tip p sk seed prf hash j=pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) j := by
    rw [tip,pkGenStep,hashEq,prfEq]
    rfl
  change stream.digest N finalState ⦃ out => bytes out.val=Spec.shake256
    ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS a)).bytes) ++ (List.range (Shake.params p).len).flatMap
      (pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a))) (Shake.params p).n ⦄
  rw [plen,show (Shake.params p).n=N.val from hp.n,← addr,← funext root]
  exact ok.digest N finalState _ done

end slhdsa.NativeShakeWots
