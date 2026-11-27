import Cachepath.NativeShakeWots.Hashes
import Cachepath.NativeShakeWots.Program
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [machine : Machine] [accel : Dispatch machine]

theorem stepTags (N : Usize) (ids : Array U64 machine.width) (hi : U64) :
    core.array.Array.map (keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64 N) ids hi ⦃ out =>
      ∀ l<machine.width.val, out.val[l]!.bv = ids.val[l]!.bv ||| hi.bv ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width _ hi
      (fun l (v : U64) => v.bv=ids.val[l]!.bv ||| hi.bv) ?_)
  · intro a h l hl; simpa only [Array.getElem!_Nat_eq] using h l hl
  intro i hi'
  simp only [keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64,
    keygen.closure_1.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut,lift,bind_ok]
  step as ⟨x,read⟩
  rw [read,← getElem!_pos]
  rfl

def Chains {N : Usize} (p : params.Params) (seed : Array U8 N) (a : address.Adrs)
    (chainId : Nat → U32) (initial : Nat → Spec.Bytes) (active steps : Nat) (state : Matrix machine.width) :=
  ∀ l<active, digest N state l = Spec.chain (Shake.params p) (initial l) 0 steps (bytes seed.val)
    (adrsS {a with word2:=chainId l})

theorem chain_rounds {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N) (a : address.Adrs)
    (sw aw : Array U64 4#usize) (w2 ids : Array U64 machine.width) (active : Usize)
    (chainId : Nat → U32) (initial : Nat → Spec.Bytes) (s : Matrix machine.width)
    (bounded : active.val≤machine.width.val) (swOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k)
    (awOk : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (word2 : ∀ l<active.val, w2.val[l]!.bv=addressWord a 2)
    (idOk : ∀ l<active.val, ids.val[l]!.bv=addressLow (chainId l))
    (started : Chains p seed a chainId initial active.val 0 s)
    (permutes : ActiveCorrect machine accel.permute) :
    keygen_loop0_loop0 N ⟨0#u32,15#u32⟩ sw aw w2 s active ids ⦃ out =>
      Chains p seed a chainId initial active.val 15 out ⦄ := by
  unfold keygen_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Matrix machine.width => 15-q.1.start.val)
    (inv := fun q => q.1.end=15#u32 ∧ q.1.start.val≤15 ∧ Chains p seed a chainId initial active.val q.1.start.val q.2)
  · rintro ⟨it,st⟩ ⟨last,le,prior⟩
    simp only at last le prior ⊢
    unfold keygen_loop0_loop0.body
    by_cases more : it.start.val<15
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [last];exact more) as ⟨_,next,tag,idx,ends⟩
      simp only [tag,ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
      step as ⟨hi,_,bits⟩
      step with stepTags N ids hi as ⟨tags,tagged⟩
      step as ⟨w0,v0⟩
      step as ⟨w1,v1⟩
      step with refill_layout N st sw w0 w1 w2 tags hp.le32 as ⟨packed,cells⟩
      step with permutes packed active bounded as ⟨out,permed⟩
      refine ⟨ends.trans last,by omega,?_,by omega⟩
      intro l live
      have laneFits := live.trans_le bounded
      obtain ⟨raw,dig,stored⟩ := digest_words (N:=N) st (by have := hp.le32;omega) (aligned_hash hp)
      have computed := packed_fips seed raw.val[l]! a (chainId l) it.start sw w0 w1 w2 tags (cell st) packed out l
        hp.le32 (aligned_hash hp) swOk (by rw [v0,← getElem!_pos]; exact awOk 0 (by decide))
        (by rw [v1,← getElem!_pos];exact awOk 1 (by decide)) (word2 l live)
        (by rw [tagged l laneFits,idOk l live];exact congrArg (fun x => addressLow (chainId l) ||| x) bits)
        (fun k hk => (stored l laneFits k hk).symm) (fun k hk => cells k hk l laneFits) (permed l live)
      rw [idx,chain_succ,← prior l live,computed]
      rw [dig l laneFits]
      simp [digest,Spec.F,Shake.params,paramsS_n,hp.n_eq,adrsS,List.append_assoc]
    · obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by rw [last]; change 15 ≤ it.start.val; omega))
      simp [no,tag,show it.start.val=15 by omega] at prior ⊢
      exact prior
  · exact ⟨rfl,by simp,started⟩

theorem prf_lanes {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (sw skw : Array U64 4#usize) (w0 w1 : U64) (w2 ids : Array U64 machine.width) (s : Matrix machine.width)
    (active : Usize) (chainId : Nat → U32) (bounded : active.val≤machine.width.val)
    (swOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k)
    (skOk : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k)
    (a0 : w0.bv=addressWord a 0) (a1 : w1.bv=addressWord a 1)
    (a2 : ∀ l<active.val, w2.val[l]!.bv=addressWord a 2)
    (idOk : ∀ l<active.val, ids.val[l]!.bv=addressLow (chainId l))
    (permutes : ActiveCorrect machine accel.permute) :
    (do let packed ← fill_prf N s sw skw w0 w1 w2 ids
        accel.permute packed active) ⦃ out => ∀ l<active.val, digest N out l = Spec.PRF (Shake.params p)
          (bytes seed.val) (bytes sk.val) {adrsS a with word2:=(chainId l).val,word3:=0} ⦄ := by
  step with fill_layout N s sw skw w0 w1 w2 ids hp.le32 as ⟨st,cells⟩
  step with permutes st active bounded as ⟨out,permed⟩
  rename_i l live
  have hash := packed_fips seed sk a (chainId l) 0#u32 sw w0 w1 w2 ids (fun j _ => skw.val[j]!.bv)
    st out l hp.le32 (aligned_hash hp) swOk a0 a1 (a2 l live) (by rw [show wordTag 0#u32 = 0#64 by decide,idOk l live]; exact BitVec.or_zero.symm)
    skOk (fun k hk => cells k hk l (live.trans_le bounded)) (permed l live)
  simpa [Spec.PRF,Shake.params,adrsS,paramsS_n,hp.n_eq,List.append_assoc] using hash

end slhdsa.NativeShakeWots
