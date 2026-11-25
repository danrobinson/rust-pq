import Parallel.SignJoinRoundTrip
import Parallel.SigningCoverage
open Lean Elab Command
open slhdsa.ParallelSigning.Coverage
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let worker := [`slhdsa.ParallelRawWorker.inputs,`slhdsa.ParallelForestPack.pack_fors,
    `AuthTableLinux.slhdsa.ParallelAuthTable.auth_table,`slhdsa.ParallelRawChunks.fill,
    `slhdsa.ParallelAuthTable.issuedMetadata,`slhdsa.ParallelAuthTable.issuedNode,`slhdsa.ParallelLeafTable.leaves,`slhdsa.ParallelXmssTicket.build_layers,
    `slhdsa.ParallelRootWalk.all_roots,`RootTableArm.slhdsa.shake.xmss.hash2,
    `ThreeLane.slhdsa.WidthEight.Ticket.phaseTwo,`slhdsa.ParallelSignTicket.ticket,
    `slhdsa.NativeShakeWots.sign,`slhdsa.ParallelSignJoin.run_loop0]
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal,`slh_sign,`sign,`sign_deterministic,`roundtrip] do
      let root := `ParallelLinuxArmAPI ++ suite ++ op
      reaches root worker
      excludes root `slhdsa.ParallelSignJoin.interpreted
      excludes root `slhdsa.WidthEight.Ticket.observedInputs
  reaches `slhdsa.ParallelSignJoin.enabled_bytes worker
