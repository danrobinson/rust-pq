import Armwide.RecoveryDispatch
import Armwide.XmssSigner
import Slhdsa.Proofs.Ht
import Lean

namespace slhdsa.Armwide.Hypertree
open Lean Meta

/-- Rebuild the scalar callers and proofs around implementation constants whose
first two arguments are the Arm feature records. Each declaration is checked by
the kernel with both feature records universally quantified. -/
private partial def rebuild (destination strip : Name) (modules : List Name)
    (names : IO.Ref (Std.HashMap Name Name)) (src : Name) : MetaM Name := do
  if let some target := (← names.get).get? src then return target
  let env ← getEnv
  let some mod := env.getModuleIdxFor? src | return src
  unless modules.any (·.isPrefixOf env.header.moduleNames[mod]!) do return src
  let info ← getConstInfo src
  let some body := info.value? true | return src
  let mut changed := false
  for c in info.type.getUsedConstants ++ body.getUsedConstants do
    if (← rebuild destination strip modules names c) != c then changed := true
  unless changed do
    names.modify (·.insert src src)
    return src
  let mapping ← names.get
  let target := destination ++ src.replacePrefix strip Name.anonymous
  withLocalDecl `cpu .instImplicit (mkConst ``Public.Dispatcher.Cpu) fun cpu =>
    withLocalDecl `features .instImplicit (mkConst ``Keygen.Features) fun features => do
      let replace := fun (e : Expr) => e.replace fun
        | .const c lv => (mapping.get? c).bind fun subject =>
          if c == subject then none else some (mkApp2 (mkConst subject lv) cpu features)
        | _ => none
      let type ← mkForallFVars #[cpu,features] (replace info.type)
      let value ← mkLambdaFVars #[cpu,features] (replace body)
      let decl ← match info with
      | .defnInfo d => pure <| Declaration.defnDecl { d with «name» := target, type, value, all := [target] }
      | .thmInfo t => pure <| Declaration.thmDecl { t with «name» := target, type, value }
      | _ => throwError "unexpected declaration in hypertree replay: {src}"
      addDecl decl
  names.modify (·.insert src target)
  return target

/-- Specialize source-linked proof terms using the two independent Arm feature records.
Each binding must take the CPU and compression feature records as its first two
parameters. Unchanged roots are rejected so an unintended scalar proof cannot
silently satisfy a requested platform root. -/
def replayFeatures (destination : Name) (bindings : List (Name × Name)) (roots : Array Name)
    (modules : List Name) : MetaM Unit := do
  let names ← IO.mkRef (Std.HashMap.ofList bindings)
  for root in roots do
    let target ← rebuild destination Name.anonymous modules names root
    unless target == destination ++ root do
      throwError "Arm feature replay did not specialize requested root {root} as {destination ++ root}"

def buildHypertree : MetaM Unit := do
  let names ← IO.mkRef (Std.HashMap.ofList [
    (`slhdsa.wots.wots_pk_from_sig,`slhdsa.Armwide.Recovery.Dispatcher.wots.wots_pk_from_sig),
    (`slhdsa.wots_pk_from_sig_spec,`slhdsa.Armwide.Hypertree.wots_pk_from_sig_spec),
    (`slhdsa.xmss.xmss_sign,`slhdsa.Armwide.XmssLeaves.Signer.xmss.xmss_sign),
    (`slhdsa.xmss_sign_spec,`slhdsa.Armwide.XmssLeaves.Signer.xmss_sign_spec)])
  for root in [`slhdsa.xmss_pk_from_sig_spec,`slhdsa.ht_verify_spec,`slhdsa.ht_sign_spec] do
    discard <| rebuild `slhdsa.Armwide.Hypertree `slhdsa [`Slhdsa] names root

end slhdsa.Armwide.Hypertree
