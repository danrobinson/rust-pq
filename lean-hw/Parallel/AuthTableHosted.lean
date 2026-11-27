import Parallel.AuthTable
import Parallel.RootTableHosted

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,root) in [(`AuthTableApple,`RootTableApple),(`AuthTableLinux,`RootTableArm),(`AuthTableX86,`RootTableX86)] do
    let hash := `slhdsa.shake.xmss.hash2
    let spec := `slhdsa.Shake.hash2_spec
    PlatformProof.replay dst [(hash,root ++ hash),(spec,root ++ spec)] #[`slhdsa.ParallelAuthTable.published_auth]
      [`Parallel.AuthTable,`Parallel.AuthTableRow,`Parallel.AuthTableProgram,`Parallel.ReduceNative,`Parallel.ReduceNativeProgram]
    for required in [`slhdsa.ParallelAuthTable.auth_table,`slhdsa.ParallelAuthTable.read_node,`slhdsa.ParallelReduceNative.shakeFamily] do
      unless (← getEnv).contains (dst ++ required) do throwError "missing native XMSS table component {dst ++ required}"
