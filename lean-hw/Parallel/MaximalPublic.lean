import Parallel.MaximalSession
import Parallel.WidthEightRoundTrip
open Lean Elab Command Meta
open slhdsa.MaximalWorker
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    let params := mkConst (`slhdsa.sets ++ suite ++ `params.PARAMS)
    for src in [`ParallelAppleAPI,`ParallelX86API,`ParallelLinuxArmAPI] do
      let linux := src == `ParallelLinuxArmAPI
      let ops := if linux then [`slh_sign_internal,`slh_sign,`sign,`sign_deterministic,`roundtrip] else
        [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec,`roundtrip]
      for fromPrefix in [false,true] do
        let histTy := mkApp (mkConst (if fromPrefix then ``StartFor else ``For)) params
        let install (args : Array Expr) : MetaM Unit := do
          withLocalDeclD (if fromPrefix then `prefixes else `histories) histTy fun h => do
            let session ← if fromPrefix then mkAppM ``Beginning.complete #[h] else pure h
            let schedules ← mkAppM ``Session.schedules #[session]
            let dst := (if fromPrefix then `PrefixSigning else `MaximalSigning) ++ src ++ suite
            for op in ops do
              let checked := mkApp (mkAppN (mkConst (src ++ suite ++ op)) args) schedules
              let value ← mkLambdaFVars (args.push h) checked
              addDecl <| .thmDecl {«name» := dst ++ op,levelParams := [],type := ← inferType value,value}
        if src == `ParallelAppleAPI then withLocalDeclD `sha3 (mkConst `Bool) fun flag => install #[flag]
        else install #[]
