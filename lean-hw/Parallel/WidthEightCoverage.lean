import Parallel.WidthEightRoundTrip
import Parallel.WidthEightTicketHosted
open Lean Elab Command
namespace slhdsa.WidthEight.ParallelSign.Coverage

private partial def visit (env : Environment) (declName : Name) : StateM NameSet Unit := do
  if (←get).contains declName then return
  modify (·.insert declName)
  let some idx := env.getModuleIdxFor? declName | return
  unless [`Buffered,`Parallel,`Shakebatch,`Shakeopt,`Slhdsa,`Facade,`Cachepath,`Fused].any (·.isPrefixOf env.header.moduleNames[idx]!) do return
  if let some (.defnInfo d) := env.find? declName then
    for child in d.value.getUsedConstants do visit env child

private def reaches (root : Name) (required : List Name) : CoreM Unit := do
  let env ← getEnv
  let info ← getConstInfo root
  let (_,seen) := (info.type.getUsedConstants.toList.forM (visit env)).run {}
  for child in required do
    unless seen.contains child do throwError "{root} does not reach {child}. Candidates: {seen.toList.filter (fun n => n.toString.endsWith child.getString!)}"

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for apple in [true,false] do
      let host := if apple then `ParallelApple else `ParallelX86
      let api := (if apple then `ParallelAppleAPI else `ParallelX86API) ++ suite
      let ticket := if apple then `TicketApple else `TicketX86
      let engine := (if apple then `WidthEightAppleKeys else `WidthEightX86Keys) ++ `slhdsa.WidthEight.sourceEngine
      let sponge := if apple then `AppleSingleStream.KappleouterRust.shake256.Sponge.absorb else `KxouterRust.shake256.Sponge.absorb
      let worker := [`slhdsa.ParallelCaller.Sh.signWith,host ++ `slhdsa.ParallelCaller.Sh.shake.slh.slh_sign_internal,`slhdsa.ParallelSignJoin.replay,`slhdsa.ParallelSignJoin.interpreted,
        `slhdsa.ParallelSignJoin.run,`slhdsa.ParallelSignJoin.run_loop0,sponge]
      for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do reaches (api ++ op) worker
      reaches (api ++ `roundtrip) (engine :: `slhdsa.WidthEight.verify :: worker)
      reaches (ticket ++ `slhdsa.WidthEight.Ticket.from_layers)
        [`slhdsa.ParallelXmssTicket.build_layers,ticket ++ `slhdsa.WidthEight.Ticket.ticket,`slhdsa.NativeShakeWots.sign,sponge]

end slhdsa.WidthEight.ParallelSign.Coverage
