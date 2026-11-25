import Shakebatch.WidthEightSession
open Lean Meta Elab Command

namespace slhdsa.WidthEight

/- Specialize both dimensions, including the platform argument retained in
the generic sponge replay, for each named public entry and seed session. -/
set_option Elab.async false in
run_cmd liftTermElabM do
  let install (n : Name) (args : Array Expr) (proof : Expr) : MetaM Unit := do
    let value ← mkLambdaFVars args proof
    addDecl <| .thmDecl {«name» := n, levelParams := [], type := ← inferType value, value}
  for s in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for apple in [true,false] do
      let publish (host : Expr) (args : Array Expr) : MetaM Unit := do
        let dst := (if apple then `WidthEightAppleAPI else `WidthEightX86API) ++ s
        let scope := (if apple then `WidthEightApple else `WidthEightX86) ++ `WidthEightSDK
        for op in [`sign_spec,`sign_deterministic_spec,`verify_spec,`slh_sign_spec,`slh_verify_spec,
                   `slh_sign_internal_spec,`slh_verify_internal_spec] do
          let base := `slhdsa ++ s ++ op
          let root := if (← getEnv).contains (scope ++ `SegmentedPublic ++ base)
            then scope ++ `SegmentedPublic ++ base else scope ++ base
          let proof := mkApp (mkConst root) host
          install (dst ++ op) args proof
        let p := mkConst (`slhdsa.sets ++ s ++ `params.PARAMS)
        let hp := mkConst (`slhdsa ++ s ++ `pn)
        let cert ← mkAppM ``seeded_accepts #[host]
        forallBoundedTelescope (← inferType cert) (some 2) fun xs _ => do
          let proof ← mkAppOptM ``seeded_accepts #[some host,some xs[0]!,some xs[1]!,none,some p,some hp]
          install (dst ++ `seeded_roundtrip) (args ++ xs) proof
      if apple then
        withLocalDeclD `sha3 (mkConst `Bool) fun sha3 =>
          publish (mkApp (mkConst ``Platform.apple) sha3) #[sha3]
      else publish (mkConst ``Platform.x86) #[]

end slhdsa.WidthEight
