import Fused.Prepare
import Fused.Forest
import Fused.Written
import Fused.AuthSuffix
open Aeneas Aeneas.Std Result
namespace slhdsa.Fused
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
set_option maxHeartbeats 2500000
variable [kernel : Kernel]
local instance entryMachine : Machine := machine kernel

private def finishRows (N : Usize) (pk : Matrix 8#usize) (pos : Usize) := do
  let padded ← xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ pk pos
  let final ← kernel.permute padded
  NativeVerify.ActiveHash.read_active N final 8#usize

def staged {N : Usize} (p : params.Params) (m sk : Array U8 N) (idx : U32)
    (seed : Array U8 N) (a : address.Adrs) : Result (alloc.vec.Vec U8) := do
  let v ← prepare p m sk idx seed a
  let (sig,pk,pos) ← xmss_sign_batch_loop2 N 8#usize ⟨0#usize,v.len⟩ v.digits v.n v.sw v.skw
    v.lane v.w0 v.w1 v.prf v.hash v.sig v.pk v.offset (Array.repeat 25#usize (Array.repeat 8#usize 0#u64))
  let rows ← finishRows N pk pos
  auth_suffix p sk idx seed a v.len v.lane v.base sig rows

theorem raw_eq {N : Usize} (p : params.Params) (m sk : Array U8 N) (idx : U32)
    (seed : Array U8 N) (a : address.Adrs) :
    xmss_sign_batch p m sk idx seed a = staged p m sk idx seed a := by
  simp only [xmss_sign_batch,staged,prepare,finishRows,Stream.init,auth_suffix,lift,bind_tc_eq,Std.bind_assoc,bind_ok]
  rfl

private theorem spec_address (a : address.Adrs) (base l : Nat) (fits : base+l<2^32) :
    adrsS (laneAddress a address.WOTS_HASH base l) =
      {(adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair:=base+l} := by
  unfold adrsS laneAddress Spec.Adrs.setTypeAndClear address.WOTS_HASH Spec.WOTS_HASH
  congr 1 <;> first | rfl | exact Nat.mod_eq_of_lt fits

theorem sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) (height : 3≤p.hp.val)
    (bound : idx.val<2^p.hp.val) (perms : Permutes kernel) (active : ActiveCorrect (machine kernel) kernel.active)
    (subtree : SubtreeAt p sk seed a) :
    xmss_sign_batch p m sk idx seed a ⦃ out => bytes out.val =
      Spec.xmssSign (Shake.params p) (bytes m.val) (bytes sk.val) idx.val (bytes seed.val) (adrsS a) ⦄ := by
  rw [raw_eq]
  unfold staged
  step with prepare_spec p hp m sk idx seed a as ⟨v,r⟩
  have fit : v.lane.val<8 := r.lane ▸ Nat.mod_lt _ (by decide)
  have cap : v.len.val+p.hp.val≤128 := by have := r.count; have := hp.le32; have h : p.hp.val≤9 := hp.valid.hp_le; omega
  have rate : v.offset.val<17 := by have := r.off; have := r.width; have := hp.le32; omega
  have count : v.len.val=(Shake.params p).len := r.count.trans hp.len.symm
  step with forest p hp sk seed a v.base.val v.digits v.len v.n v.sw v.skw v.lane v.w0 v.w1 v.prf v.hash
    v.sig v.pk v.offset _ r.len r.width fit (v.len.val+p.hp.val) (by omega) cap r.size r.valid r.prf r.hash
    r.secret rate (fun l h => by simpa [streamPrefix] using r.sponge l h) perms as ⟨sig,pk,pos,written,rate',streamed⟩
  have finish := Stream.finish_keys p hp sk seed (fun l => adrsS (laneAddress a address.WOTS_HASH v.base.val l))
    pk pos rate' perms (fun l hl => by simpa only [streamPrefix,tip,count] using streamed l hl)
  change finishRows N pk pos ⦃ _ ⦄ at finish
  step with finish as ⟨rows,keys⟩
  have small : idx.val<512 := bound.trans_le (Nat.pow_le_pow_right (by decide) hp.valid.hp_le)
  have addr (l : Nat) (hl : l<8) := spec_address a v.base.val l (by have := r.base; omega)
  have selected : v.base.val+v.lane.val=idx.val := by have := r.base; have := r.lane; omega
  have digitsLen : v.len.val=v.digits.val.length := r.len
  have front := written_wots p hp m sk seed _ v.digits.val _ v.sig sig (digitsLen ▸ written)
    (by omega) (digitsLen.symm.trans count) r.decoded
  rw [←digitsLen] at front
  apply WP.spec_mono (suffix_correct p hp sk idx seed a v.len v.lane v.base sig rows _ subtree active
    height bound r.base r.lane (by rw [written.1,Nat.add_mul]) front (by
      intro j hj
      simpa only [Spec.xmssNode,←addr j hj] using keys j hj))
  intro out h
  rw [h,Spec.xmssSign,addr _ fit,selected]
  rfl

end slhdsa.Fused
