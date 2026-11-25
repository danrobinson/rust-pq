import Buffered.SmallTags
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify NativeVerify.Wots NativeShakeWots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1800000
variable [kernel : Fused.Kernel]
local instance shortChainsMachine : Machine := Fused.machine kernel

private theorem steps (N K : Usize) (ids : Array U64 8#usize) (hi : U64) :
    core.array.Array.map (leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64 N K) ids hi ⦃ out =>
      ∀ l<8, out.val[l]!.bv = ids.val[l]!.bv ||| hi.bv ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize _ hi
      (fun l (v : U64) => v.bv=ids.val[l]!.bv ||| hi.bv) ?_)
  · intro a h l hl; simpa only [Array.getElem!_Nat_eq] using h l hl
  intro i hi'
  simp only [leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64,
    leaves.closure.Insts.CoreOpsFunctionFnMutTupleU64U64.call_mut,lift,bind_ok]
  step as ⟨x,read⟩
  rw [read,← getElem!_pos]
  rfl

private def values {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (first : U32)
    (K idx : Usize) (active steps : Nat) (state : Matrix 8#usize) :=
  ∀ l<active, digest N state l = Fused.chainValue p seed (Fused.laneAddress a address.WOTS_HASH first.val)
    (chainId K idx l) (Fused.seedValue p sk seed a first.val (chainId K idx l)) steps ((idx.val+l)%K.val)

private theorem rounds {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (first : U32) (K idx active : Usize) (sw : Array U64 4#usize) (w0 w1 : U64)
    (hash ids : Array U64 8#usize) (state : Matrix 8#usize) (bounded : active.val≤8)
    (seedOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k)
    (lo : w0.bv=addressWord a 0) (hi : w1.bv=addressWord a 1)
    (hashOk : ∀ l<active.val, hash.val[l]!.bv=addressWord (keyAddr a address.WOTS_HASH first K idx l) 2)
    (idOk : ∀ l<active.val, ids.val[l]!.bv=addressLow (chainId K idx l))
    (started : values p sk seed a first K idx active.val 0 state)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    leaves_loop2_loop1 N K ⟨0#u32,15#u32⟩ sw w0 w1 state active hash ids ⦃ out =>
      values p sk seed a first K idx active.val 15 out ⦄ := by
  unfold leaves_loop2_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Matrix 8#usize => 15-q.1.start.val)
    (inv := fun q => q.1.end=15#u32 ∧ q.1.start.val≤15 ∧ values p sk seed a first K idx active.val q.1.start.val q.2)
  · rintro ⟨it,st⟩ ⟨last,le,prior⟩
    simp only at last le prior ⊢
    unfold leaves_loop2_loop1.body
    by_cases more : it.start.val<15
    · step with core.iter.range.IteratorRange.next_U32_some_spec it (by rw [last];exact more) as ⟨_,next,tag,inc,ends⟩
      simp only [tag,ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
      step as ⟨top,_,bits⟩
      step with steps N K ids top as ⟨w3,tagged⟩
      step with refill_layout N st sw w0 w1 hash w3 hp.le32 as ⟨packed,cells⟩
      step with perm packed active bounded as ⟨out,permed⟩
      refine ⟨ends.trans last,by omega,?_,by omega⟩
      intro l live
      have laneFits := live.trans_le bounded
      obtain ⟨raw,dig,stored⟩ := digest_words (N:=N) st (by have := hp.le32;omega) (aligned_hash hp)
      have computed := packed_fips seed raw.val[l]! (keyAddr a address.WOTS_HASH first K idx l) (chainId K idx l)
        it.start sw w0 w1 hash w3 (cell st) packed out l hp.le32 (aligned_hash hp) seedOk lo hi (hashOk l live)
        (by rw [tagged l laneFits,idOk l live];exact congrArg (fun x => addressLow (chainId K idx l) ||| x) bits)
        (fun k hk => (stored l laneFits k hk).symm) (fun k hk => cells k hk l laneFits) (permed l live)
      simp only [values,Fused.chainValue] at prior
      unfold Fused.chainValue
      rw [inc,chain_succ,←prior l live,computed,dig l laneFits]
      simp [digest,Spec.F,Shake.params,paramsS_n,hp.n_eq,adrsS,keyAddr,List.append_assoc]
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by rw [last];change 15 ≤ it.start.val;omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact (show it.start.val=15 by omega) ▸ prior
  · exact ⟨rfl,by change 0≤15;decide,started⟩

/-- One active packed group in the small leaf routine, up to the WOTS endpoint stream. -/
def batch {N : Usize} (K idx active : Usize) (first : U32) (sw skw : Array U64 4#usize) (w0 w1 : U64)
    (state : Matrix 8#usize) (prf hash ids : Array U64 8#usize) := do
  let (prf,hash,ids) ← leaves_loop2_loop0 K ⟨0#usize,active⟩ first idx prf hash ids
  let packed ← fill_prf N state sw skw w0 w1 prf ids
  let start ← kernel.active packed active
  let steps ← params.W - 1#u32
  leaves_loop2_loop1 N K ⟨0#u32,steps⟩ sw w0 w1 start active hash ids

theorem batch_tips {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (first : U32) (K idx active : Usize) (sw skw : Array U64 4#usize) (w0 w1 : U64)
    (state : Matrix 8#usize) (prf hash ids : Array U64 8#usize)
    (pos : 0<K.val) (keys : K.val≤8) (fit : first.val+K.val≤2^32) (cap : idx.val+active.val≤512)
    (bounded : active.val≤8) (seedOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k)
    (keyOk : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k)
    (lo : w0.bv=addressWord a 0) (hi : w1.bv=addressWord a 1)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    batch (N:=N) K idx active first sw skw w0 w1 state prf hash ids ⦃ out =>
      ∀ l<active.val, digest N out l = Fused.tip p sk seed a first.val ((idx.val+l)%K.val) ((idx.val+l)/K.val) ⦄ := by
  unfold batch
  step with chain_tags K idx active first a prf hash ids pos keys fit cap bounded as ⟨ans,tagged⟩
  obtain ⟨ps,hs,is'⟩ := ans
  dsimp only at tagged ⊢
  step with fill_layout N state sw skw w0 w1 ps is' hp.le32 as ⟨packed,cells⟩
  step with perm packed active bounded as ⟨start,permed⟩
  have initial : values p sk seed a first K idx active.val 0 start := by
    intro l live
    have computed := packed_fips seed sk (keyAddr a address.WOTS_PRF first K idx l) (chainId K idx l)
      0#u32 sw w0 w1 ps is' (fun j _ => skw.val[j]!.bv) packed start l hp.le32 (aligned_hash hp)
      seedOk lo hi (tagged l live).1 (by rw [show wordTag 0#u32=0#64 by decide,(tagged l live).2.2];exact BitVec.or_zero.symm)
      keyOk (fun k hk => cells k hk l (live.trans_le bounded)) (permed l live)
    simpa [Fused.chainValue,Spec.chain,Fused.seedValue,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,
      adrsS,keyAddr,List.append_assoc] using computed
  have sub : params.W - 1#u32 = ok 15#u32 := by rw [W_eq];rfl
  simp only [sub,bind_tc_eq,bind_ok]
  with_unfolding_all change leaves_loop2_loop1 N K ⟨0#u32,15#u32⟩ sw w0 w1 start active hs is' ⦃ out => ∀ l<active.val, digest N out l = Fused.tip p sk seed a first.val ((idx.val+l)%K.val) ((idx.val+l)/K.val) ⦄
  apply WP.spec_mono (rounds p hp sk seed a first K idx active sw w0 w1 hs is' start bounded seedOk lo hi
    (fun l hl => (tagged l hl).2.1) (fun l hl => (tagged l hl).2.2) initial perm)
  intro out produced l hl
  rw [produced l hl,Fused.tip_value]
  have bound : (idx.val+l)/K.val<2^32 := (Nat.div_le_self _ _).trans_lt (by omega)
  have eq : (chainId K idx l).val=(idx.val+l)/K.val := Nat.mod_eq_of_lt bound
  rw [eq]
end slhdsa.Buffered.SmallWots
