import Shakebatch.WidthThreeVerify
import Shakebatch.WidthThreeParallel
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree

/-- The segmented signing and verification proofs support every representable slice.
The inherited SDK wrappers pass their old contiguous allocation hypothesis to a
proof that ignores it. Rechecking the proof bodies after weakening that hypothesis
shows that every named wrapper is valid over the wider domain. -/
def allLengths (_ _ : Slice U8) := True

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let mut claims : Array (Name × Name) := #[]
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`sign,`slh_sign,`sign_deterministic,`verify,`slh_verify] do
      let verify := op == `verify || op == `slh_verify
      let host := if verify then `WidthThreeVerifySDK else `WidthThreeLinuxSDK.WidthThreeSDK
      let original := host ++ `SegmentedPublic.slhdsa ++ setName ++ Name.mkSimple (op.toString ++ "_spec")
      let root := `slhdsa.WidthThree.AllLengths ++ setName ++ op
      claims := claims.push (original,root)
      unless verify do
        let parallel := `WidthThreeParallel.SegmentedPublic.slhdsa ++ setName ++ Name.mkSimple (op.toString ++ "_spec")
        claims := claims.push (parallel, `slhdsa.WidthThree.ParallelAllLengths ++ setName ++ op)
  let target := `AllSlices
  PlatformProof.replay target [(`slhdsa.Shake.ContextFits,`slhdsa.WidthThree.allLengths)]
    (claims.map Prod.fst) [`Cachepath,`Shakeopt]
  for (original,root) in claims do
    let weakened ← getConstInfo (target ++ original)
    forallTelescope weakened.type fun xs post => do
      let args := xs.pop
      unless (← isDefEq (← inferType xs.back!) (mkConst `True)) do
        throwError "the original allocation constraint still occurs in {original}"
      let proof := mkApp (mkAppN (mkConst (target ++ original)) args) (mkConst `True.intro)
      let type ← mkForallFVars args post
      let value ← mkLambdaFVars args proof
      addDecl <| .thmDecl {«name» := root, levelParams := [], type, value}

end slhdsa.WidthThree
