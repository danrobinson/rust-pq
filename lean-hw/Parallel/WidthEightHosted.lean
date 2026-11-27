import Parallel.WidthEightSigning
import Parallel.WidthEightTicketHosted
open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut roots := #[`slhdsa.WidthEight.ParallelSign.worker_returns,`slhdsa.WidthEight.ParallelSign.internal_uses_worker,`slhdsa.WidthEight.ParallelSign.context_uses_worker]
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do
      let base := `slhdsa ++ suite ++ op
      let previous := if (←getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      roots := roots.push (`WidthEightParallel ++ previous)
  for (dst,existing,pairs) in [
      (`ParallelApple,`WidthEightApple,←Cachepath.NativeHashReplay.appleBindings),
      (`ParallelX86,`WidthEightX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let env ← getEnv
    let mut known := pairs
    for (n,_) in env.constants.toList do
      let ticket := if dst == `ParallelApple then `TicketApple else `TicketX86
      let ns := if ticket.isPrefixOf n then ticket else existing
      if ns.isPrefixOf n then
        let original := n.replacePrefix ns Name.anonymous
        if env.contains original then known := (original,n)::known
    PlatformProof.replay dst known roots [`Parallel.WidthEightSigning,`Parallel.PhaseTwoRoots,`Parallel.PhaseTwoJoin,`Parallel.PhaseTwoWrites,`Parallel.UncachedProgram,`Parallel.UncachedCaller,
      `Parallel.SegmentedCaller,`Cachepath,`Shakeopt]
    unless (←getEnv).contains (dst ++ `slhdsa.ParallelCaller.Sh.shake.slh.slh_sign_internal) &&
        (←getEnv).contains (dst ++ `slhdsa.ParallelCaller.Sh.shake.slh.shake_sign_ctx) do
      throwError "missing both native message hashing paths in {dst}"
