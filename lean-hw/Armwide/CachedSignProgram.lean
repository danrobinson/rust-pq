import Armwide.ForsTree.Sign
import Armplatform.WideForsDispatch
import Armwide.Hypertree
import Armplatform.Internal
import Cachepath.EndToEnd

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.CachedSign
open Public.Dispatcher (Cpu)
open Keygen (Features)
noncomputable section
abbrev wotsSign [cpu : Cpu] [_f : Features] {N : Usize} := @Public.Dispatcher.wots.wots_sign cpu N
abbrev forsRecover [cpu : Cpu] [f : Features] {N : Usize} := @WideFors.dispatch N (ok cpu.wide) f.sha512 f.sha512
abbrev seedCtx [_c : Cpu] [_f : Features] {N : Usize} := @slhdsa.hash.seed_ctx N
end

open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  Hypertree.replayFeatures `ArmCached [
    (`slhdsa.hash.seed_ctx,`slhdsa.Armwide.CachedSign.seedCtx),
    (`slhdsa.wots.wots_sign,`slhdsa.Armwide.CachedSign.wotsSign),
    (`slhdsa.fors.fors_pk_from_sig,`slhdsa.Armwide.CachedSign.forsRecover),
    (`slhdsa.fors.fors_sign,`slhdsa.ArmForsTree.Entry.fors.fors_sign),
    (`slhdsa.xmss.xmss_sign,`slhdsa.Armwide.XmssLeaves.Signer.xmss.xmss_sign),
    (`slhdsa.xmss.xmss_pk_from_sig,`slhdsa.Armwide.Hypertree.xmss.xmss_pk_from_sig)]
    #[`CacheopsRust.cache.sha2_ops.sign_from_digest] [`Cacheops]

theorem wots_hit_spec [cpu : Cpu] [f : Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (reach : Public.hashAddress (slhdsa.adrsS a) = slhdsa.adrsS a) :
    wotsSign m sk seed a ⦃ r => slhdsa.bytes r.val = Spec.wotsSign (paramsS p) (slhdsa.bytes m.val)
      (slhdsa.bytes sk.val) (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ∧ r.length=N.val*(2*N.val+3) ⦄ := by
  unfold wotsSign
  rw [Public.Dispatcher.wots_dispatch_eq p hp m sk seed hs a reach]
  exact slhdsa.wots_sign_spec p hp m sk seed hs a

theorem normalized_wots [cpu : Cpu] [f : Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (layer : U32) (tree : U64) (leaf : U32) :
    let addr := CacheopsRust.toSlhAdrs ⟨layer,tree,CacheopsRust.address.WOTS_HASH,leaf,0#u32,0#u32⟩
    wotsSign m sk seed addr ⦃ r => slhdsa.bytes r.val = Spec.wotsSign (paramsS p) (slhdsa.bytes m.val)
      (slhdsa.bytes sk.val) (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS addr) ∧ r.length=N.val*(2*N.val+3) ⦄ :=
  wots_hit_spec p hp m sk seed hs _ (by with_unfolding_all rfl)

end slhdsa.Armwide.CachedSign
