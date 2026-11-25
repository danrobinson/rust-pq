import Parallel.SigningCoverage
import Parallel.WidthEightRoundTrip
import Parallel.PhaseTwoHosted
open Lean Elab Command
namespace slhdsa.WidthEight.ParallelSign.Coverage

open slhdsa.ParallelSigning.Coverage

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for apple in [true,false] do
      let host := if apple then `ParallelApple else `ParallelX86
      let api := (if apple then `ParallelAppleAPI else `ParallelX86API) ++ suite
      let ticket := if apple then `TicketApple else `TicketX86
      let table := (if apple then `AuthTableApple else `AuthTableX86) ++ `slhdsa.ParallelAuthTable.auth_table
      let engine := (if apple then `WidthEightAppleKeys else `WidthEightX86Keys) ++ `slhdsa.WidthEight.sourceEngine
      let sponge := if apple then `AppleSingleStream.KappleouterRust.shake256.Sponge.absorb else `KxouterRust.shake256.Sponge.absorb
      let worker := [`slhdsa.ParallelCaller.Sh.signWith,host ++ `slhdsa.ParallelCaller.Sh.shake.slh.slh_sign_internal,`slhdsa.ParallelSignJoin.replayWith,`slhdsa.ParallelRawWorker.inputs,`slhdsa.ParallelForestPack.pack_fors,
    `slhdsa.ParallelAuthTable.issuedMetadata,`slhdsa.ParallelAuthTable.issuedNode,`slhdsa.ParallelLeafTable.leaves,table,
        `slhdsa.ParallelRawChunks.fill,
        host ++ `slhdsa.WidthEight.Ticket.phaseTwo,ticket ++ `slhdsa.WidthEight.Ticket.ticket,
        `slhdsa.ParallelXmssTicket.build_layers,`slhdsa.ParallelRootWalk.all_roots,
        `slhdsa.ParallelSignJoin.run,`slhdsa.ParallelSignJoin.run_loop0,sponge]
      for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do
        reaches (api ++ op) worker
        excludes (api ++ op) `slhdsa.ParallelSignJoin.interpreted
        excludes (api ++ op) `slhdsa.WidthEight.Ticket.observedInputs
      excludes (api ++ `roundtrip) `slhdsa.ParallelSignJoin.interpreted
      reaches (api ++ `roundtrip) (engine :: `slhdsa.WidthEight.verify :: worker)
      reaches (ticket ++ `slhdsa.WidthEight.Ticket.from_layers)
        [`slhdsa.ParallelXmssTicket.build_layers,ticket ++ `slhdsa.WidthEight.Ticket.ticket,`slhdsa.NativeShakeWots.sign,sponge]
  for apple in [true,false] do
    let afterJoin := if apple then `PhaseTwoApple else `PhaseTwoX86
    let ticket := if apple then `TicketApple else `TicketX86
    let hash := if apple then `RootTableApple.slhdsa.shake.xmss.hash2 else `RootTableX86.slhdsa.shake.xmss.hash2
    let parallel := if apple then `ParallelApple else `ParallelX86
    reaches (parallel ++ `slhdsa.WidthEight.ParallelSign.worker_returns)
      [parallel ++ `slhdsa.WidthEight.Ticket.phaseTwo,ticket ++ `slhdsa.WidthEight.Ticket.ticket,
       `slhdsa.ParallelRootWalk.all_roots,hash,`slhdsa.ParallelSignJoin.run_loop0]
    for op in [`internal_from_forest,`context_from_forest] do
      reaches (afterJoin ++ `slhdsa.WidthEight.Ticket ++ op)
        [(if apple then `ParallelApple else `ParallelX86) ++ `slhdsa.WidthEight.Ticket.phaseTwo,`slhdsa.WidthEight.Ticket.writeRows,
         ticket ++ `slhdsa.WidthEight.Ticket.ticket,`slhdsa.ParallelXmssTicket.build_layers,
         `slhdsa.ParallelRootWalk.all_roots,hash,`slhdsa.ParallelSignJoin.run_loop0]

end slhdsa.WidthEight.ParallelSign.Coverage
