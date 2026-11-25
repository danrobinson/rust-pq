import Shakebatch.WidthThreeLinux

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree

structure ParallelPrimitives extends SigningPrimitives where
  worker : ParallelCaller.Worker ParallelCaller.ShakeSeed
  published {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) :
    ParallelCaller.WorkerCorrect worker (N:=N) p (Shake.params p) (fun s => bytes s.val) (fun _ => True)

noncomputable abbrev parallelInternal (s : ParallelPrimitives) :=
  @WidthThreeLinux.slhdsa.ParallelCaller.Sh.shake.slh.slh_sign_internal
    (WidthThreeLinux.slhdsa.WidthThree.fallback s.wots s.fors) s.worker

noncomputable abbrev parallelContext (s : ParallelPrimitives) :=
  @WidthThreeLinux.slhdsa.ParallelCaller.Sh.shake.slh.shake_sign_ctx
    (WidthThreeLinux.slhdsa.WidthThree.fallback s.wots s.fors) s.worker

theorem internalSpec (s : ParallelPrimitives) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) :
    parallelInternal s p m sk rnd ⦃ out =>
      bytes out.val=Spec.slhSignInternal (Shake.params p) (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧
      out.length=(paramsS p).sigBytes ⦄ :=
  @WidthThreeLinux.slhdsa.WidthThree.parallel_sign_spec s.wots s.fors s.worker N p hp m sk rnd hsk (s.published p hp)

theorem contextSpec (s : ParallelPrimitives) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) (hc : ctx.length≤255) :
    parallelContext s p m ctx sk rnd ⦃ out =>
      bytes out.val=Spec.slhSignInternal (Shake.params p) (Spec.withContext (bytes m.val) (bytes ctx.val))
        (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @WidthThreeLinux.slhdsa.WidthThree.parallel_context_spec s.wots s.fors s.worker N p hp m ctx sk rnd hsk hc (s.published p hp)

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let names ← IO.mkRef (Std.HashMap.ofList [
    (`slhdsa.shake.slh.slh_sign_internal, `slhdsa.WidthThree.parallelInternal),
    (`slhdsa.Shake.slh_sign_internal_all_lengths, `slhdsa.WidthThree.internalSpec),
    (`ShakeoptSeg.shake.slh.shake_sign_ctx, `slhdsa.WidthThree.parallelContext),
    (`Shakeopt.Segmented.shake_sign_ctx_spec, `slhdsa.WidthThree.contextSpec)])
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do
      let base := `slhdsa ++ setName ++ op
      let goal := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthThreeParallel [`Slhdsa,`Shakebatch,`Shakeopt]
        goal names `slhdsa.WidthThree.ParallelPrimitives
      unless actual == `WidthThreeParallel ++ goal do throwError "missed parallel SHAKE signing entry {goal}"

end slhdsa.WidthThree
