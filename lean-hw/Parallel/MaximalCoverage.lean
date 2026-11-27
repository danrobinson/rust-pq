import Parallel.MaximalEnabled
import Parallel.SigningCoverage

open Lean Elab Command slhdsa.ParallelSigning.Coverage

/-
Inspect theorem statements, following the functions that execute the signer.
A proof restricted to a serial fallback or a prepopulated slot table must not
satisfy the coverage checks for the worker, signing wrappers and round trips.
-/
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for host in [`ParallelAppleAPI,`ParallelX86API,`ParallelLinuxArmAPI] do
    let linux := host == `ParallelLinuxArmAPI
    let ops := if linux then [`slh_sign_internal,`slh_sign,`sign,`sign_deterministic] else
      [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec]
    for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
      for kind in [`MaximalSigning,`PrefixSigning] do
        let checked := [`slhdsa.MaximalWorker.Session.schedules,`slhdsa.MaximalWorker.Maximal.schedule,
          `slhdsa.RawFors.nativeAction,`slhdsa.ParallelRawChunks.fill,`slhdsa.ParallelLeafTable.leaves,
          `slhdsa.ParallelRootWalk.all_roots,`slhdsa.ParallelSignJoin.run_loop0]
        let required := if kind == `PrefixSigning then `slhdsa.MaximalWorker.Beginning.complete :: checked else checked
        for op in [`worker_returns,`roundtrip] ++ ops do
          reaches (kind ++ host ++ suite ++ op) required
