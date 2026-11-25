import Parallel.PhaseTwoPublic
import Parallel.WidthEightTicketHosted
import Parallel.WidthEightHosted

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,hosted,prior,bindings) in [
      (`PhaseTwoApple,`ParallelApple,`TicketApple,←Cachepath.NativeHashReplay.appleBindings),
      (`PhaseTwoX86,`ParallelX86,`TicketX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let mut known := bindings
    let env ← getEnv
    for ns in [hosted,prior] do
      for (n,_) in env.constants.toList do
        if ns.isPrefixOf n then
          let orig := n.replacePrefix ns Name.anonymous
          if env.contains orig then known := (orig,n)::known
    PlatformProof.replay dst known #[`slhdsa.WidthEight.Ticket.internal_from_forest,
      `slhdsa.WidthEight.Ticket.context_from_forest,`slhdsa.WidthEight.Ticket.joined_from_forest]
      [`Parallel.PhaseTwoPublic,`Parallel.PhaseTwoRoots,`Parallel.PhaseTwoJoin,`Parallel.PhaseTwoWrites,
       `Parallel.UncachedCaller,`Parallel.SegmentedCaller,`Parallel.SignJoin]
    unless (←getEnv).contains (dst ++ `slhdsa.WidthEight.Ticket.phaseTwo) do
      throwError "missing hosted worker writes in {dst}"
