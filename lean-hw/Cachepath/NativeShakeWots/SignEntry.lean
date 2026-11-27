import Cachepath.NativeShakeWots.SignInitSchedule
import Cachepath.NativeShakeWots.SignInitPrf
import Shakebatch.WotsDispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify NativeVerify.Wots Signer
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine] [accel : Dispatch machine]

theorem sign_digits {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (digits : Slice U32) (positive : 0<machine.width.val) (permutes : ActiveCorrect machine accel.permute)
    (bound : digits.length≤67) (valid : ∀ i<digits.length, digits.val[i]!.val<16)
    (domain : a.typ=address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    sign sk seed a digits ⦃ out => bytes out.val=(List.range digits.length).flatMap (signedChain p sk seed a digits.val) ∧
      out.length=digits.length*N.val ⦄ := by
  have small := hp.le32
  have align := aligned_hash hp
  unfold sign
  step as ⟨n,count⟩
  step as ⟨offset,off⟩
  step with seed_spec seed small as ⟨sw,seedWords⟩
  step with seed_spec sk small as ⟨skw,skWords⟩
  step as ⟨prfT,_,prfTypes⟩
  step as ⟨prf,prfFields⟩
  step with address_spec prf as ⟨ap,prfWords⟩
  step as ⟨hashT,_,hashTypes⟩
  step as ⟨hash,hashFields⟩
  step with address_spec hash as ⟨ah,hashWords⟩
  step as ⟨w,vp⟩
  step as ⟨sz,szv⟩
  step as ⟨sig,sv⟩
  step as ⟨iter,generated,stride⟩
  have iterEq : iter=⟨⟨0#usize,digits.len⟩,machine.width⟩ := by cases iter;congr
  rw [iterEq]
  have sigLen : sig.length=digits.length*N.val := by
    have h := congrArg List.length sv
    simpa [List.length_replicate,szv,Nat.mul_comm] using h
  rw [← getElem!_pos] at vp
  have seedOk (k : Nat) (h : k<N.val/8) := (seedWords k (by omega)).trans (ite_eq_left h)
  obtain ⟨⟨sig1,table,s⟩,prfRun,prepared⟩ := spec_imp_exists (prepare_secrets p hp sk seed digits prf digits.len n rfl bound count sw skw ap (Array.repeat machine.width w)
    _ sig _ sigLen positive seedOk (fun k h => by simpa [h] using skWords k (by omega)) prfWords
    (fun l h => by rw [Array.repeat_val];simpa [h,vp] using prfWords 2 (by decide)) permutes)
  rw [prfRun,bind_ok]
  try dsimp only
  obtain ⟨⟨order,total⟩,sortRun,sorted⟩ := spec_imp_exists (Signer.schedule_sort digits bound valid)
  simp only [sortRun,lift,bind_tc_eq,bind_ok,uncurry]
  try dsimp only
  try simp only [lift,bind_ok]
  let c := makeSchedule digits n order total table (secretAt p sk seed prf) sig1 small align count bound valid sorted prepared
  let active := core.cmp.impls.OrdUsize.min total machine.width
  have cnt : active.val=min total.val machine.width.val := by
    change (if machine.width < total then machine.width else total).val=_
    split <;> rename_i h
    · exact (min_eq_right (Nat.le_of_lt h)).symm
    · exact (min_eq_left (Nat.le_of_not_gt h)).symm
  have room : active.val≤machine.width.val := by omega
  have cap : active.val≤c.total.val := by change _≤total.val;omega
  obtain ⟨⟨next,ids,steps,ends,vals⟩,laneRun,pos,lanes⟩ := spec_imp_exists (initialize_lanes c active
    (Array.repeat machine.width 0#usize) (Array.repeat machine.width 0#u32) (Array.repeat machine.width 0#u32)
    (Array.repeat machine.width (Array.repeat 4#usize 0#u64)) room cap)
  change sign_loop1 ⟨0#usize,active⟩ digits table order 0#usize _ _ _ _ = ok _ at laneRun
  rw [laneRun]
  simp only [bind_ok,uncurry]
  step as ⟨pad,pv⟩
  have inc := sorted.2.2.2
  have launched := launch p hp c seed hash offset pad sw ah sig1 next active ids steps ends vals s cnt pos lanes
    prepared (fun i _ => by simp [c,makeSchedule,secretAt,Spec.PRF,Shake.params,hp.n_eq]) positive off pv
    (fun k h => seedOk k (by change k<n.val at h;omega)) hashWords sorted.2.2.1 inc permutes
  apply WP.spec_mono launched
  rintro out ⟨len,rows⟩
  refine ⟨signed_bytes out ⟨len,?_⟩ ?_,len⟩
  · intro i hi _ b hb
    have hashEq : hash=a := by
      rw [hashFields,hashTypes]
      obtain ⟨layer,tree,typ,pair,w2,w3⟩ := a
      obtain ⟨t,x,y⟩ := domain
      simp only at t x y
      subst typ;subst w2;subst w3;rfl
    have prfEq : adrsS prf=Spec.wotsSkAdrs (adrsS a) := by
      simp [prfFields,prfTypes,adrsS,Spec.wotsSkAdrs,Spec.Adrs.setTypeAndClear,Spec.WOTS_PRF,WOTS_PRF_eq]
    have eq : expected c p seed hash i=signedChain p sk seed a digits.val i := by
      simp only [expected,c,makeSchedule,secretAt,Signer.Schedule.ending,signedChain,hashEq,prfEq]
      rfl
    rw [← eq]
    exact rows i hi b hb
  · intro j
    unfold signedChain
    cases digit : (digits.val[j]!).val with
    | zero => simp [Spec.chain,Spec.PRF,Shake.params,hp.n_eq]
    | succ n => rw [chain_succ];simp [Spec.F,Shake.params,hp.n_eq]

theorem sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (positive : 0<machine.width.val) (permutes : ActiveCorrect machine accel.permute) :
    (do let ds ← wots.wots_digits m; sign sk seed a ds.deref) ⦃ out => bytes out.val=
      Spec.wotsSign (Shake.params p) (bytes m.val) (bytes sk.val) (bytes seed.val) (adrsS a) ∧
      out.length=N.val*(2*N.val+3) ⦄ := by
  let* ⟨ds,hd,len,small⟩ ← wots_digits_spec p hp m
  have view : ds.deref=ds.slice := by apply Slice.ext;simp [alloc.vec.Vec.deref,Slice.from_val];rfl
  have hn := hp.le32
  have actual : ds.slice.length=2*N.val+3 := len
  rw [view]
  let* ⟨out,rows,size⟩ ← sign_digits p hp sk seed a ds.slice positive permutes (by omega) (fun i hi => by
    apply small; rw [getElem!_pos ds.slice.val i hi]; exact List.getElem_mem ..) domain
  refine ⟨?_,by simpa only [actual,Nat.mul_comm] using size⟩
  change nats ds.val = Spec.wotsDigits (Shake.params p) (bytes m.val) at hd
  change bytes out.val = (List.range (Shake.params p).len).flatMap (signStep _ _ _ _ (Spec.wotsDigits _ _))
  rw [rows,show (Shake.params p).len=ds.slice.length from hp.len.trans actual.symm,← hd]
  apply List.flatMap_congr
  intro i hi
  have bound : i<ds.val.length := List.mem_range.mp hi
  simp only [signedChain,signStep,nats_getElem! _ _ bound];rfl

end slhdsa.NativeShakeWots
