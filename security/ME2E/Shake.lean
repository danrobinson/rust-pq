import ME2E.Basic
import MLink.ShakePrimitives
import MLink.Replay

/-! Recheck the generic key-generation, signing and verification proofs with the six
SHAKE hash laws, the full address key, and the SHAKE parameter row. -/
set_option maxRecDepth 8192 in
run_cmd Lean.Elab.Command.liftCoreM do
  ShakeProof.replay `ShakeLink
    [(`MLink.Sha2Set.spec, `ShakeSecurity.params),
     (`MLink.Sha2Set.prims, `ShakeSecurity.prims),
     (`SLHDSA.Concrete.sha2Primitives, `ShakeSecurity.primitives),
     (`SLHDSA.Concrete.sha2WireCodec, `ShakeSecurity.wireCodec),
     (`MLink.F_eq, `ShakeSecurity.F_eq),
     (`MLink.H_eq, `ShakeSecurity.H_eq),
     (`MLink.Tl_eq, `ShakeSecurity.Tl_eq),
     (`MLink.PRF_eq, `ShakeSecurity.PRF_eq),
     (`MLink.PRFmsg_eq, `ShakeSecurity.PRFmsg_eq),
     (`MLink.Hmsg_eq, `ShakeSecurity.Hmsg_eq)]
    #[`ME2E.keygen_transfer, `ME2E.sign_transfer, `ME2E.verify_transfer,
      `ME2E.signPure_transfer, `ME2E.verifyPure_transfer]
