import Fused.StreamPrefix
import Fused.ChainValues
open Aeneas Aeneas.Std Result
namespace slhdsa.Fused
open ShakeBatch NativeVerify
variable [kernel : Kernel]
local instance prepareMachine : Machine := machine kernel
set_option linter.concreteInstances false
set_option maxHeartbeats 1600000

structure Inputs where
  digits : alloc.vec.Vec U32
  len : Usize
  n : Usize
  offset : Usize
  sw : Array U64 4#usize
  skw : Array U64 4#usize
  base : U32
  lane : Usize
  w0 : U64
  w1 : U64
  prf : Array U64 8#usize
  hash : Array U64 8#usize
  sig : alloc.vec.Vec U8
  pk : Matrix 8#usize

def prepare {N : Usize} (p : params.Params) (m sk : Array U8 N) (idx : U32) (seed : Array U8 N)
    (a : address.Adrs) : Result Inputs := do
  let ds ← wots.wots_digits m
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let sw ← seed_words seed
  let skw ← seed_words sk
  let base := idx &&& (~~~ (7#u32))
  let lane := UScalar.cast .Usize (idx &&& 7#u32)
  let words ← adrs_words a
  let w0 ← Array.index_usize words 0#usize
  let w1 ← Array.index_usize words 1#usize
  let pkTag ← core.array.from_fn 8#usize (xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) base
  let prf ← core.array.from_fn 8#usize (xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) base
  let hash ← core.array.from_fn 8#usize (xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) base
  let count ← params.Params.xmss_sig_bytes p
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 count
  let pk ← Stream.init n sw w0 w1 pkTag
  ok ⟨ds, ds.len, n, offset, sw, skw, base, lane, w0, w1, prf, hash, sig, pk⟩

structure Ready {N : Usize} (p : params.Params) (m sk : Array U8 N) (idx : U32) (seed : Array U8 N)
    (a : address.Adrs) (v : Inputs) : Prop where
  decoded : nats v.digits.val = Spec.wotsDigits (Shake.params p) (bytes m.val)
  len : v.len.val = v.digits.length
  count : v.len.val = 2*N.val+3
  valid : ∀ i < v.digits.length, v.digits.val[i]!.val ≤ 15
  width : v.n.val = N.val/8
  off : v.offset.val = v.n.val+4
  base : v.base.val = 8*(idx.val/8)
  lane : v.lane.val = idx.val%8
  prf : Header seed (laneAddress a address.WOTS_PRF v.base.val) v.sw v.w0 v.w1 v.prf
  hash : Header seed (laneAddress a address.WOTS_HASH v.base.val) v.sw v.w0 v.w1 v.hash
  secret : ∀ k < N.val/8, v.skw.val[k]!.bv=inputWord sk.val k
  size : v.sig.length = (v.len.val+p.hp.val)*N.val
  sponge : ∀ l < 8, (ShakeBatch.lane v.pk l,8*v.offset.val)=
    (bytes seed.val ++ (Spec.wotsPkAdrs (adrsS (laneAddress a address.WOTS_HASH v.base.val l))).bytes).foldl
      Spec.Keccak.feed Spec.Keccak.initial

theorem prepare_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) :
    prepare p m sk idx seed a ⦃ v => Ready p m sk idx seed a v ⦄ := by
  let base := idx &&& (~~~ (7#u32))
  let lane := UScalar.cast .Usize (idx &&& 7#u32)
  have small := hp.le32
  have inputBound : idx.val < 4294967296 := idx.hBounds
  obtain ⟨mask,aligned⟩ := lane_bits idx
  have baseFit : base.val+8 ≤ 2^32 := by change (idx &&& (~~~ (7#u32))).val+8 ≤ 4294967296; omega
  have laneEq : lane.val=idx.val%8 := by
    dsimp [lane]
    simpa using mask
  unfold prepare
  let* ⟨digits,decoded,count,valid⟩ ← wots_digits_spec p hp m
  step as ⟨n,width⟩
  step as ⟨pos,off⟩
  step with seed_spec seed small as ⟨sw,words⟩
  step with seed_spec sk small as ⟨skw,secret⟩
  step with address_spec a as ⟨ar,addr⟩
  step as ⟨w0,rd0⟩
  step as ⟨w1,rd1⟩
  have lo : w0.bv=addressWord a 0 := by rw [rd0,←getElem!_pos]; exact addr 0 (by decide)
  have hi : w1.bv=addressWord a 1 := by rw [rd1,←getElem!_pos]; exact addr 1 (by decide)
  step with pk_lanes N a base baseFit as ⟨tag,tagEq⟩
  step with prf_lanes N a base baseFit as ⟨prf,prfEq⟩
  step with hash_lanes N a base baseFit as ⟨hash,hashEq⟩
  step with xmss_sig_bytes_spec p hp.valid as ⟨size,sizeEq,_⟩
  step as ⟨sig,initSig,sigLen⟩
  have seedWords (k : Nat) (hk : k < N.val/8) : sw.val[k]!.bv=inputWord seed.val k := by
    simpa only [hk,ite_true] using words k (by omega)
  step with Stream.init_keys p hp seed a base.val n pos sw w0 w1 tag width off
    (fun k hk => seedWords k (by omega)) lo hi tagEq as ⟨pk,ready⟩
  all_goals try scalar_tac
  have digitsLen : digits.len.val=digits.length := rfl
  refine ⟨decoded,digitsLen,digitsLen.trans count,?_,width,off,?_,laneEq,?_,?_,?_,?_,ready⟩
  · intro i inside
    have d := valid digits.val[i]! (by rw [getElem!_pos digits.val i inside]; exact List.getElem_mem ..)
    exact Nat.le_of_lt_succ d
  · change (idx &&& (~~~ (7#u32))).val = _; omega
  · exact ⟨seedWords,fun _ _ => lo,fun _ _ => hi,prfEq⟩
  · exact ⟨seedWords,fun _ _ => lo,fun _ _ => hi,hashEq⟩
  · intro k hk; simpa only [hk,ite_true] using secret k (by omega)
  · change sig.length = (digits.len.val+p.hp.val)*N.val
    rw [digitsLen,count,sigLen,sizeEq,hp.n_eq]

end slhdsa.Fused
