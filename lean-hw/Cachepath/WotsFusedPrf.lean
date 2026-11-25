import Cachepath.WotsFusedChain
open Aeneas Aeneas.Std Result
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [machine : Machine]

def PrfStable {N : Usize} (seed sk : Array U8 N) (addresses : Array address.Adrs machine.width) (s : Matrix machine.width) :=
  ∀ k<25, k ≠ N.val/8+4-1 → ∀ j<machine.width.val, cell s k j =
    if N.val/8+4 ≤ k ∧ k < N.val/8+4+N.val/8 then inputWord sk.val (k-(N.val/8+4)) else baseWord seed addresses.val[j]! k

def inner (count offset chain : Usize) (prf input : Matrix machine.width) :
    Result (Matrix machine.width × Matrix machine.width × Matrix machine.width) := do
  let c ← lift (UScalar.cast .U32 chain)
  let swapped ← core.num.U32.swap_bytes c
  let id ← lift (core.convert.num.FromU64U32.from swapped)
  let r ← offset - 1#usize
  let tagged ← Array.update prf r (Array.repeat machine.width id)
  let state ← machine.permute tagged
  let stop ← params.W - 1#u32
  let pair ← generate_loop0_loop0 count ⟨0#u32,stop⟩ offset input id state
  ok (tagged,pair.1,pair.2)

def tip {N : Usize} (p : params.Params) (sk seed : Array U8 N) (prfAddr hashAddr : address.Adrs) (chain : Nat) :=
  Spec.chain (Shake.params p)
    (Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val) {adrsS prfAddr with word2:=chain,word3:=0})
    0 15 (bytes seed.val) {adrsS hashAddr with word2:=chain}

theorem addresses_spec {N : Usize} (keys : Array U32 machine.width) (a : address.Adrs) (typ : U32) :
    generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call (N:=N) (keys,a) typ ⦃ out =>
      ∀ j<machine.width.val, out.val[j]! = {a with typ:=typ,keypair:=keys.val[j]!,word2:=0#u32,word3:=0#u32} ⦄ := by
  unfold generate.closure.Insts.CoreOpsFunctionFnTupleU32ArrayAdrsW.call
  apply map_spec (generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) keys (a,typ) (fun j v => v = {a with typ:=typ,keypair:=keys.val[j]!,word2:=0#u32,word3:=0#u32})
  intro j hj
  simp [generate.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut,address.Adrs.with_type,address.Adrs.with_keypair,step_simps]

theorem init_input {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (addrs : Array address.Adrs machine.width) (size : Usize) (sz : size.val=2*N.val+32) :
    ShakeBatch.shake.batch.header seed addrs size ⦃ out => Stable seed addrs out ⦄ := by
  have small := hp.le32
  apply WP.spec_mono (header_spec seed addrs size small (by omega))
  intro s head k hk _ _ j hj
  simpa [baseWord,sz] using head k hk j hj

theorem init_prf {N : Usize} (p : params.Params) (hp : PN p N) (seed sk : Array U8 N)
    (addrs : Array address.Adrs machine.width) (size offset : Usize) (sz : size.val=2*N.val+32)
    (off : offset.val=N.val/8+4) :
    (do let raw ← ShakeBatch.shake.batch.header seed addrs size
        ShakeBatch.shake.batch.put raw offset (Array.repeat machine.width sk)) ⦃ out => PrfStable seed sk addrs out ⦄ := by
  have small := hp.le32
  step with header_spec seed addrs size small (by omega) as ⟨raw,head⟩
  step with put_spec raw offset (Array.repeat machine.width sk) (by omega) as ⟨placed,put⟩
  intro k hk _ j hj
  rw [put k hk j hj,head k hk j hj,off,sz,Array.repeat_val]
  simp [hj,baseWord]

theorem inner_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (count offset chain : Usize) (countEq : count.val=N.val/8) (offsetEq : offset.val=N.val/8+4)
    (chainFit : chain.val<2^32) (sk seed : Array U8 N)
    (prfAddrs hashAddrs : Array address.Adrs machine.width) (prf input : Matrix machine.width)
    (prfGood : PrfStable seed sk prfAddrs prf) (inputGood : Stable seed hashAddrs input)
    (permutes : PermutationCorrect) :
    inner count offset chain prf input ⦃ tag next hashed =>
      PrfStable seed sk prfAddrs tag ∧ Stable seed hashAddrs next ∧
        DigestIs (N:=N) hashed (fun j => tip p sk seed prfAddrs.val[j]! hashAddrs.val[j]! chain.val) ⦄ := by
  let c := UScalar.cast .U32 chain
  let id : U64 := core.convert.num.FromU64U32.from
    ((c.bv.extractLsb' 0 8 ++ c.bv.extractLsb' 8 8 ++ c.bv.extractLsb' 16 8 ++ c.bv.extractLsb' 24 8)#uscalar)
  have cast : c.val=chain.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ chainFit
  have idEq : id.bv=addressLow c := rfl
  have small := hp.le32
  unfold inner
  simp only [lift,bind_ok,core.num.U32.swap_bytes]
  step as ⟨r,rv⟩
  step as ⟨tag,tagv⟩
  step with permutes tag as ⟨state,permed⟩
  have row (k j : Nat) (hj : j<machine.width.val) : cell tag k j =
      if k=N.val/8+4-1 then addressLow c else cell prf k j := by
    rw [tagv,write_tag _ r id (by omega) k j hj,rv,offsetEq,idEq]
  have preserved : PrfStable seed sk prfAddrs tag := by
    intro k hk other j hj
    rw [row k j hj,ite_eq_right other,prfGood k hk other j hj]
  let root := fun (j : Nat) => Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val)
    {adrsS prfAddrs.val[j]! with word2:=chain.val,word3:=0}
  have dig : DigestIs (N:=N) state root := by
    intro j hj
    have eq := hashed_short seed sk prfAddrs.val[j]! c 0#u32 tag state j hp.le32 (aligned_hash hp) (permed j hj) (by
      intro k hk
      rw [row k j hj]
      by_cases tagged : k=N.val/8+4-1
      · have outside : ¬(N.val/8+4≤k ∧ k<N.val/8+4+N.val/8) := by omega
        simp [tagged,wordTag]
      · rw [ite_eq_right tagged,prfGood k hk tagged j hj,ite_eq_right tagged])
    simpa [root,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,adrsS,cast,List.append_assoc] using eq
  have stop : params.W - 1#u32 = ok 15#u32 := by rw [W_eq]; rfl
  rw [stop,bind_ok]
  step with chain_spec p hp count offset countEq offsetEq id c idEq seed hashAddrs root input state inputGood dig permutes as ⟨pair,stable,done⟩
  refine ⟨preserved,stable,?_⟩
  intro j hj
  have addrEq (a : address.Adrs) : adrsS {a with word2:=c} = {adrsS a with word2:=chain.val} := by
    cases a
    simp only [adrsS,cast]
  exact (done j hj).trans (congrArg (Spec.chain (Shake.params p) (root j) 0 15 (bytes seed.val)) (addrEq _))

end slhdsa.cache.builder.nativeShake.Vector.Fused
