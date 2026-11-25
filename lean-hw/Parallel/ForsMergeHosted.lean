import Parallel.ForsMerge
import Parallel.RootTableHosted

open Lean Elab Command in
set_option Elab.async false in
run_cmd liftCoreM do
  for host in [`RootTableApple, `RootTableArm, `RootTableX86] do
    let dst := host ++ `ForsMerge
    let names := [`slhdsa.shake.xmss.hash2, `slhdsa.Shake.hash2_spec]
    PlatformProof.replay dst (names.map fun n => (n, host ++ n))
      #[`slhdsa.ParallelForsMerge.merge_spec]
      [`Parallel.ForsMerge, `Parallel.ForsMergeProgram, `Parallel.ReduceNative]
    unless (← getEnv).contains (dst ++ `slhdsa.ParallelForsMerge.merge_fors) do
      throwError "missing hosted split-FORS reducer in {dst}"
