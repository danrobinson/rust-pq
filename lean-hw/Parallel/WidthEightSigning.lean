import Parallel.WidthEightSome
import Shakebatch.WidthEightSession
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.ParallelSign
open ParallelCaller ParallelSignJoin
noncomputable section

structure Config where
  host : Platform
  threads : Usize

@[instance_reducible] def fallback (h : Platform) : Sh.Fallback where
  forsSign := @WidthEight.forsSign h
  forsRecover := @WidthEight.forsRecover h
  htSign := @WidthEight.htSign h

theorem fallback_correct (h : Platform) {N : Usize} (p : params.Params) (hp : PN p N) :
    Sh.FallbackCorrect (fallback h) (N:=N) p :=
  ⟨WidthEight.forsSign_spec h p hp,WidthEight.forsRecoverSpec h p hp,WidthEight.htSignSpec h p hp⟩

abbrev internal (c : Config) := @Sh.shake.slh.slh_sign_internal (fallback c.host) (replay c.threads)
abbrev context (c : Config) := @Sh.shake.slh.shake_sign_ctx (fallback c.host) (replay c.threads)

theorem internal_spec (c : Config) {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) :
    internal c p m sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
      (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @Sh.sign_spec (fallback c.host) (replay c.threads) N p hp m sk rnd hsk (fallback_correct c.host p hp)
    ((projectedPublished c.threads).published p hp)

theorem context_spec (c : Config) {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) (hc : ctx.length≤255) :
    context c p m ctx sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
      (Spec.withContext (bytes m.val) (bytes ctx.val)) (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @Sh.sign_ctx_spec (fallback c.host) (replay c.threads) N p hp m ctx sk rnd hsk hc
    (fallback_correct c.host p hp) ((projectedPublished c.threads).published p hp)

theorem internal_uses_worker (c : Config) (enabled : 2≤c.threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets) (other : Sh.Fallback)
    (m sk : Slice U8) (rnd : Array U8 N) :
    internal c p m sk rnd = @Sh.shake.slh.slh_sign_internal other (replay c.threads) N p m sk rnd :=
  fallback_irrelevant c.threads enabled p hp member _ other m sk rnd _ _

theorem context_uses_worker (c : Config) (enabled : 2≤c.threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets) (other : Sh.Fallback)
    (m ctx sk : Slice U8) (rnd : Array U8 N) :
    context c p m ctx sk rnd = @Sh.shake.slh.shake_sign_ctx other (replay c.threads) N p m ctx sk rnd :=
  fallback_irrelevant c.threads enabled p hp member _ other m sk rnd _ _

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let names ← IO.mkRef (Std.HashMap.ofList [
    (`slhdsa.shake.slh.slh_sign_internal,`slhdsa.WidthEight.ParallelSign.internal),
    (`slhdsa.Shake.slh_sign_internal_all_lengths,`slhdsa.WidthEight.ParallelSign.internal_spec),
    (`ShakeoptSeg.shake.slh.shake_sign_ctx,`slhdsa.WidthEight.ParallelSign.context),
    (`Shakeopt.Segmented.shake_sign_ctx_spec,`slhdsa.WidthEight.ParallelSign.context_spec)])
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do
      let base := `slhdsa ++ setName ++ op
      let goal := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthEightParallel [`Slhdsa,`Shakebatch,`Shakeopt]
        goal names `slhdsa.WidthEight.ParallelSign.Config
      unless actual == `WidthEightParallel ++ goal do throwError "missing public parallel signer {goal}"

end
end slhdsa.WidthEight.ParallelSign
