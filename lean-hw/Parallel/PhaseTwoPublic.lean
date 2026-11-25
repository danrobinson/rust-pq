import Parallel.PhaseTwoRoots
import Parallel.WidthEightSigning

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket
open ParallelCaller ParallelSignJoin

noncomputable def signer (host : Platform) (threads : Usize) (first : ForestWorker) :=
  worker threads (completedJoin host (rootsFrom host first))

theorem internal_from_forest (host : Platform) (threads : Usize) (first : ForestWorker)
    {N : Usize} (p : params.Params) (hp : PN p N) (source : ForestLaw first N p)
    (m sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) :
    @Sh.shake.slh.slh_sign_internal (ParallelSign.fallback host) (signer host threads first)
      N p m sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
        (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @Sh.sign_spec (ParallelSign.fallback host) (signer host threads first) N p hp m sk rnd hsk (ParallelSign.fallback_correct host p hp)
    (worker_correct threads _ p hp (joined_from_forest host first p hp source))

theorem context_from_forest (host : Platform) (threads : Usize) (first : ForestWorker)
    {N : Usize} (p : params.Params) (hp : PN p N) (source : ForestLaw first N p)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) (hc : ctx.length≤255) :
    @Sh.shake.slh.shake_sign_ctx (ParallelSign.fallback host) (signer host threads first)
      N p m ctx sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
        (Spec.withContext (bytes m.val) (bytes ctx.val)) (bytes sk.val) (bytes rnd.val) ∧
        out.length=(paramsS p).sigBytes ⦄ :=
  @Sh.sign_ctx_spec (ParallelSign.fallback host) (signer host threads first) N p hp m ctx sk rnd hsk hc (ParallelSign.fallback_correct host p hp)
    (worker_correct threads _ p hp (joined_from_forest host first p hp source))

end slhdsa.WidthEight.Ticket
