import Parallel.UncachedCaller
import Shakeopt.Segmented
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelCaller.Sh
set_option linter.concreteInstances false

variable [fallback : Fallback] [worker : Worker ShakeSeed]

def shake.slh.shake_sign_ctx {N : Usize} (p : slhdsa.params.Params) (m ctx sk : Slice U8) (rnd : Array U8 N) :=
  signWith (fun k r msg => ShakeoptSeg.shake.hash.prf_msg_ctx k r ctx msg)
    (fun p r k root msg => ShakeoptSeg.shake.hash.h_msg_ctx p r k root ctx msg) p m sk rnd

theorem sign_ctx_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (rnd : Array U8 N) (hsk : sk.length=4*N.val) (hc : ctx.length≤255)
    (ops : FallbackCorrect fallback (N:=N) p)
    (slots : WorkerCorrect worker (N:=N) p (Shake.params p) (fun s => bytes s.val) (fun _ => True)) :
    shake.slh.shake_sign_ctx p m ctx sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
      (Spec.withContext (bytes m.val) (bytes ctx.val)) (bytes sk.val) (bytes rnd.val) ∧
      out.length=(paramsS p).sigBytes ⦄ :=
  signWith_spec p hp m sk rnd hsk (Spec.withContext (bytes m.val) (bytes ctx.val)) _ _
    (fun key => Shakeopt.Segmented.prf_msg_ctx_params p hp key rnd ctx m hc)
    (fun r key root => Shakeopt.Segmented.h_msg_ctx_params p r key root ctx m hc) ops slots

end slhdsa.ParallelCaller.Sh
