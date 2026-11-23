import MLink.Replay
import MReduction.Shake
import HashSig.SLHDSA.Security.ByteBound

/-! Query-bounded single-random-oracle forging bounds specialized to the same
concrete primitive context as the extracted Rust SHAKE implementation. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
run_cmd Lean.Elab.Command.liftCoreM do
  ShakeProof.replay `ShakeIdeal [(`SLHDSA.Concrete.shakePrimitives, `ShakeSecurity.primitives),
    (`SLHDSA.Concrete.shakePrimitives_byteLaws, `ShakeSecurity.byteLaws)]
    #[`SLHDSA.Security.shakeStrongAdvantage_le_securityBound_validatedParams,
      `SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_validatedParams,
      `SLHDSA.Security.shakeAdvantage_le_securityBound_validatedParams,
      `SLHDSA.Security.shakeAdvantage_le_securityBound_hedged_validatedParams]
    [`HashSig.SLHDSA.Security]
