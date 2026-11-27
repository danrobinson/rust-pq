import Parallel.ScalarForsTicket
open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,bindings,thm) in [
      (`ScalarTicketApple,← Cachepath.NativeHashReplay.appleBindings,`slhdsa.ParallelScalarFors.wide_tickets),
      (`ScalarTicketX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86,`slhdsa.ParallelScalarFors.wide_tickets),
      (`ScalarTicketLinux,Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux,`slhdsa.ParallelScalarFors.narrow_tickets)] do
    PlatformProof.replay dst bindings #[thm] [`Parallel.ScalarForsProgram,`Parallel.ScalarForsTicket,`Cachepath,`Shakeopt]
    for required in [`slhdsa.ParallelScalarFors.node,`slhdsa.ParallelScalarFors.direct_node_ticket,
        `slhdsa.ParallelScalarFors.split_node_ticket,`slhdsa.shake.hash.thash_pair] do
      unless (←getEnv).contains (dst ++ required) do throwError "native scalar FORS provider missing: {dst ++ required}"
