import Buffered.FullForest
import Buffered.Leaves
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.Full
open ShakeBatch NativeVerify Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 2000000
variable [kernel : Fused.Kernel]
local instance : Machine := Fused.machine kernel

private def grouped {N : Usize} (sk seed : Array U8 N) (first : U32) (a : address.Adrs) := do
  let n ← N / 8#usize
  let off ← n + 4#usize
  let sw ← seed_words seed
  let skw ← seed_words sk
  let aw ← adrs_words a
  let w0 ← Array.index_usize aw 0#usize
  let w1 ← Array.index_usize aw 1#usize
  let pk ← core.array.from_fn 8#usize (xmss_sign_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) first
  let prf ← core.array.from_fn 8#usize (xmss_sign_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) first
  let hash ← core.array.from_fn 8#usize (xmss_sign_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N) first
  let sponge ← Fused.Stream.init n sw w0 w1 pk
  let twice ← 2#usize * N
  let len ← twice + params.LEN2
  let (acc,pos) ← leaves_loop1 N ⟨0#usize,len⟩ n sw skw w0 w1 prf hash sponge off
    (Array.repeat 25#usize (Array.repeat 8#usize 0#u64))
  (do let padded ← xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ acc pos
      let final ← kernel.permute padded
      NativeVerify.ActiveHash.read_active N final 8#usize)

theorem raw_eq {N : Usize} (sk seed : Array U8 N) (first : U32) (a : address.Adrs) :
    leaves sk seed first a = grouped sk seed first a := by
  simp only [grouped,leaves,Fused.Stream.init,bind_tc_eq,Std.bind_assoc,bind_ok]
  rfl

theorem leaves_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (first : U32) (a : address.Adrs) (capacity : first.val+8≤2^32) (perms : Permutes kernel) :
    leaves sk seed first a ⦃ rows => LeafRows p sk seed a first.val rows ⦄ := by
  rw [raw_eq]
  unfold grouped
  have small := hp.le32
  step as ⟨n,width⟩
  step as ⟨off,atPos⟩
  step with seed_spec seed small as ⟨sw,words⟩
  step with seed_spec sk small as ⟨skw,secret⟩
  step with address_spec a as ⟨aw,adrs⟩
  step as ⟨w0,rd0⟩
  step as ⟨w1,rd1⟩
  have lo : w0.bv=addressWord a 0 := by rw [rd0,←getElem!_pos]; exact adrs 0 (by decide)
  have hi : w1.bv=addressWord a 1 := by rw [rd1,←getElem!_pos]; exact adrs 1 (by decide)
  step with pk_lanes N a first capacity as ⟨pk,pkTag⟩
  step with prf_lanes N a first capacity as ⟨prf,prfTag⟩
  step with hash_lanes N a first capacity as ⟨hash,hashTag⟩
  have seedWords (k : Nat) (hk : k<N.val/8) : sw.val[k]!.bv=inputWord seed.val k := by
    simpa only [hk,ite_true] using words k (by omega)
  step with Fused.Stream.init_keys p hp seed a first.val n off sw w0 w1 pk width atPos
    (fun k hk => seedWords k (by omega)) lo hi pkTag as ⟨sponge,ready⟩
  step as ⟨twice,tw⟩
  simp only [LEN2_eq]
  step as ⟨len,count⟩
  have length : len.val=(Shake.params p).len := by change len.val=(paramsS p).len; rw [hp.len]; omega
  have prfHeader : Header seed (laneAddress a address.WOTS_PRF first.val) sw w0 w1 prf :=
    ⟨seedWords,fun _ _ => lo,fun _ _ => hi,prfTag⟩
  have hashHeader : Header seed (laneAddress a address.WOTS_HASH first.val) sw w0 w1 hash :=
    ⟨seedWords,fun _ _ => lo,fun _ _ => hi,hashTag⟩
  have key (k : Nat) (hk : k<N.val/8) : skw.val[k]!.bv=inputWord sk.val k := by
    simpa only [hk,ite_true] using secret k (by omega)
  have initialized (l : Nat) (hl : l<8) :
      (ShakeBatch.lane sponge l,8*off.val)=streamPrefix p sk seed a first.val l 0 := by
    simpa only [streamPrefix,List.range_zero,List.flatMap_nil,List.append_nil] using ready l hl
  obtain ⟨⟨acc,pos⟩,ran,rate,streamed⟩ := spec_imp_exists (forest_spec p hp sk seed a first.val len n sw skw
    w0 w1 prf hash sponge off (Array.repeat 25#usize (Array.repeat 8#usize 0#u64))
    (by omega) width prfHeader hashHeader key (by omega) initialized perms)
  rw [ran]
  simp only [bind_tc_eq,bind_ok]
  change (do let padded ← xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ acc pos
             let final ← kernel.permute padded
             NativeVerify.ActiveHash.read_active N final 8#usize) ⦃ rows => LeafRows p sk seed a first.val rows ⦄
  apply WP.spec_mono (Fused.Stream.finish_keys p hp sk seed (fun l => adrsS (laneAddress a address.WOTS_HASH first.val l))
    acc pos rate perms (fun l hl => by simpa only [streamPrefix,tip,length] using streamed l hl))
  intro rows keys j hj
  have eq : adrsS (laneAddress a address.WOTS_HASH first.val j) =
      {(adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair:=first.val+j} := by
    unfold adrsS laneAddress Spec.Adrs.setTypeAndClear address.WOTS_HASH Spec.WOTS_HASH
    congr 1 <;> first | rfl | exact Nat.mod_eq_of_lt (by change j<8 at hj; omega)
  rw [keys j hj,eq]
  rfl

end slhdsa.Buffered.Full
