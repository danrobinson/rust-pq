import Cachepath.NativeVerify.WotsSchedule
import Shakebatch.WotsRecover
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch Shakeopt.WotsRefill
set_option linter.concreteInstances false
set_option maxHeartbeats 1300000
variable [machine : Machine] [accel : Dispatch machine] [stream : Stream] [ok : StreamCorrect]

theorem recover_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (digits : Slice U32)
    (positive : 0<machine.width.val) (permutes : ActiveCorrect machine accel.permute)
    (count : digits.length≤67) (bounded : ∀ i < digits.length, digits.val[i]!.val≤15)
    (fits : digits.length*N.val≤sig.length) (domain : a.typ=address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    recover sig seed a digits ⦃ out => bytes out.val=Spec.shake256
      ((bytes seed.val ++ (Spec.wotsPkAdrs (adrsS a)).bytes) ++ (List.range digits.length).flatMap
        (recoveredChain p sig seed a digits.val)) N.val ⦄ := by
  have small := hp.le32
  have align := aligned_hash hp
  unfold recover
  step as ⟨n,nval⟩
  step as ⟨offset,off⟩
  step with seed_spec seed small as ⟨sw,seedWord⟩
  step as ⟨typed,_,typeFields⟩
  step as ⟨key,keyFields⟩
  have keyEq : key=a := by
    rw [keyFields,typeFields]
    obtain ⟨layer,tree,typ,pair,w2,w3⟩ := a
    obtain ⟨t,x,y⟩ := domain
    simp only at t x y
    subst typ;subst w2;subst w3;rfl
  step with address_spec key as ⟨aw,addrWord⟩
  rw [keyEq] at addrWord
  step with prepare sig digits _ _ count fits bounded as ⟨tips,remaining,ready⟩
  step as ⟨slice,view,len⟩
  step with schedule_sort sig digits slice tips remaining count ready (by simpa using len) (by simpa using view)
    as ⟨order,total,schedule⟩
  obtain ⟨queueSize,queued,unique,ordered⟩ := schedule
  simp only [bind_ok,lift]
  let active := core.cmp.impls.OrdUsize.min total machine.width
  have size : active.val=min total.val machine.width.val := core.cmp.impls.OrdUsize.min_val _ _
  let c : Schedule N := ⟨sig,digits,n,order,total,small,align,nval,count,fits,queueSize.trans count,queued⟩
  let v0 := Array.repeat machine.width (Array.repeat 4#usize 0#u64)
  let state := Array.repeat 25#usize (Array.repeat machine.width 0#u64)
  step with initialize_lanes N n active sig digits order _ _ v0 (by omega) (by omega)
    (fun l hl=>(queued l (by omega)).1) fits count (by omega) (by omega) as ⟨next,ids,steps,v,position,lanes⟩
  step as ⟨pad,padding⟩
  let g := initialGhost c tips
  have init := initial_matches c tips next active ids steps v state size position lanes
  have sem : c.semantic p seed a g := by
    apply initial_outer machine.width.val positive (Shake.params p) (bytes seed.val) (adrsS a) digits.length
      c.init c.start (fun _=>15) c.ids unique (fun i hi=>(ordered i).mp hi) (fun i=>bytes tips.val[i]!.val)
    intro i hi last
    exact congrArg bytes ((ready i hi).2 last)
  step with engine p hp c seed a offset pad sw aw g tips next active ids steps v state init sem off padding
    (by intro k hk; have hk' : k<N.val/8 := by simpa only [c,nval] using hk
        rw [seedWord k (by omega),ite_eq_left hk'])
    addrWord bounded unique ordered permutes as ⟨endpoints,done⟩
  step as ⟨typed,_,fields⟩
  step as ⟨pk,addr⟩
  step with ok.start seed pk as ⟨init,prior⟩
  step as ⟨activeRows,rows,used⟩
  simp only [Slice.len_val] at used rows
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  have found (j : Nat) (hj : j<activeRows.length) : bytes activeRows.val[j]!.val=recoveredChain p sig seed a digits.val j := by
    have hj' : j<digits.length := by omega
    have shape : activeRows.val=endpoints.val.slice 0 digits.length := by simpa using rows
    rw [shape,slice0_getElem! _ _ _ hj' (by simpa using count)]
    exact done j hj'
  step with compress_endpoints activeRows init _ _ prior found as ⟨last,absorbed⟩
  rw [used] at absorbed
  rw [← adrsS_pk a typed pk fields addr]
  exact ok.digest N last _ absorbed

end slhdsa.NativeVerify.Wots
