import Parallel.WidthEightTicket
open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,sdk,outer,bindings) in [
      (`TicketApple,`WidthEightApple,`WidthEightOuterApple,←Cachepath.NativeHashReplay.appleBindings),
      (`TicketX86,`WidthEightX86,`WidthEightOuterX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let mut known := bindings
    let env ← getEnv
    for ns in [sdk,outer] do
      for (n,_) in env.constants.toList do
        if ns.isPrefixOf n then
          let src := n.replacePrefix ns Name.anonymous
          if env.contains src then known := (src,n)::known
    PlatformProof.replay dst known #[`slhdsa.WidthEight.Ticket.published,`slhdsa.WidthEight.Ticket.from_layers]
      [`Parallel.WidthEightTicket,`Parallel.WidthEightTicketProgram,`Fused.Outer,`Fused.OuterProgram,`Cachepath,`Shakeopt]
    unless (←getEnv).contains (dst ++ `slhdsa.WidthEight.Ticket.ticket) do throwError "missing native WOTS ticket in {dst}"
