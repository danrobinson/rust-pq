import Cachepath.NativeVerify.ForsFusedLayout
import Cachepath.NativeVerify.ForsSignNode
import Shakebatch.WotsWords
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsFused
open ShakeBatch NativeVerify.Wots NativeShakeWots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine] (permute : Active machine)

private def grouped
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (active : Std.Usize)
  :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let pad ← offset + n
  let sw ← NativeVerify.seed_words seed
  let skw ← NativeVerify.seed_words sk
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let aw_prf ← NativeVerify.adrs_words a1
  let a2 ← address.Adrs.with_type addr address.FORS_TREE
  let a3 ← address.Adrs.with_keypair a2 addr.keypair
  let aw_tree ← NativeVerify.adrs_words a3
  let w3 := Array.repeat machine.width 0#u64
  let w31 ←
    fused_loop0
      { start := 0#usize, «end» := active } indices w3
  first (fun s hi => do
    let post ← permute s active
    second (fun t => do
      let result ← permute t active
      fused_loop4 ⟨0#usize,n⟩ active result (Array.repeat machine.width (Array.repeat N 0#u8)))
      n offset pad sw aw_tree w31 post hi)
    n offset pad sw skw aw_prf w31

/-- Both permutations in the native fused leaf routine produce Algorithm 15 at height zero. -/
theorem leaf_correct (perms : ActiveCorrect machine permute) : ForsSign.LeafLaw (fused permute) := by
  intro N p hp sk seed a ids active dom width
  change grouped permute sk seed a ids active ⦃ _ => _ ⦄
  unfold grouped
  step as ⟨n,nv⟩
  step as ⟨offset,off⟩
  step as ⟨pad,padding⟩
  step with seed_spec seed hp.le32 as ⟨sw,seedRead⟩
  step with seed_spec sk hp.le32 as ⟨skw,skRead⟩
  step as ⟨prfType,_,prfFields⟩
  step as ⟨prfAddr,prfKey⟩
  step with address_spec prfAddr as ⟨aw1,prfWords⟩
  step as ⟨treeType,_,treeFields⟩
  step as ⟨treeAddr,treeKey⟩
  step with address_spec treeAddr as ⟨aw2,treeWords⟩
  step with tags ids active width as ⟨w,tagged⟩
  have small := hp.le32
  have align := aligned_hash hp
  have seedWords (k : Nat) (hk : k<N.val/8) : sw.val[k]!.bv=inputWord seed.val k := by
    simpa [hk] using seedRead k (by omega)
  have skWords (k : Nat) (hk : k<N.val/8) : skw.val[k]!.bv=inputWord sk.val k := by
    simpa [hk] using skRead k (by omega)
  have tag (l : Nat) (live : l<active.val) : w.val[l]!.bv=addressLow 0#u32 ||| wordTag ids.val[l]! := by
    rw [show addressLow 0#u32=0#64 by rfl,BitVec.zero_or,tagged l live]
  have adr (aw : Array U64 4#usize) (l : Nat) (hl : l<machine.width.val) :
      (addrLane aw).val[l]!.bv=aw.val[2]!.bv := by
    simp only [addrLane,Array.repeat_val,List.getElem!_replicate _ hl]
  apply first_spec _ _ n offset pad sw skw aw1 w (by omega) off padding
  intro packed hi high cells
  step with perms packed active width as ⟨st,permuted⟩
  have firstDigest (l : Nat) (live : l<active.val) : digest N st l =
      Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) ids.val[l]!.val := by
    have lh := live.trans_le width
    have hash := packed_fips seed sk prfAddr 0#u32 ids.val[l]! sw aw1.val[0]! aw1.val[1]! (addrLane aw1) w
      (fun j _ => skw.val[j]!.bv) packed st l small align seedWords (prfWords 0 (by decide)) (prfWords 1 (by decide))
      ((adr aw1 l lh).trans (prfWords 2 (by decide))) (tag l live) skWords
      (fun k hk => nv ▸ cells k hk l lh) (permuted l live)
    simpa [prfKey,prfFields,Spec.forsSkGen,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,adrsS,
      Spec.Adrs.setTypeAndClear,Spec.FORS_PRF,fors_FORS_PRF_eq,List.append_assoc] using hash
  apply second_spec _ _ n offset pad sw aw2 w st hi (by omega) off padding high
  intro packedTree treeCells
  step with perms packedTree active width as ⟨out,treePerm⟩
  apply WP.spec_mono (read_lanes N out active n width small align nv)
  intro rows read l live
  have lh := live.trans_le width
  obtain ⟨raw,dig,stored⟩ := digest_words (N:=N) st (by omega) align
  have hash := packed_fips seed raw.val[l]! treeAddr 0#u32 ids.val[l]! sw aw2.val[0]! aw2.val[1]! (addrLane aw2) w
    (cell st) packedTree out l small align seedWords (treeWords 0 (by decide)) (treeWords 1 (by decide))
    ((adr aw2 l lh).trans (treeWords 2 (by decide))) (tag l live) (fun k hk => (stored l lh k hk).symm)
    (fun k hk => nv ▸ treeCells k hk l lh) (treePerm l live)
  rw [read l live,hash,dig l lh]
  change Spec.shake256 (_ ++ (_ ++ digest N st l)) _ = _
  rw [firstDigest l live,Spec.forsNode]
  simp [treeKey,treeFields,← dom.1,Spec.F,Shake.params,paramsS_n,hp.n_eq,adrsS,List.append_assoc]

end slhdsa.NativeVerify.ForsFused
