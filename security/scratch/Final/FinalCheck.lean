import Reduction
import E2E
open Lean Elab Command

/-!
Definition-level check for the final theorems (not part of the build; run with
`lake env lean scratch/Final/FinalCheck.lean` after `lake build Link E2E Reduction`).

For each named constant it follows definition BODIES transitively (never theorem proofs, never
the types of theorems) and reports which of the following constants are reached:
choice principles (`Classical.choice`, `Classical.indefiniteDescription`, `Exists.choose`,
`Classical.propDecidable`, `Fintype.equivFin`) and eager objects (`Reduction.sampleTable`,
`Reduction.Tables.uniformTable`, `Reduction.Tables.UniformSampler.sample`, `Fin.mOfFn`,
`Fintype.mPi`).  The last block are controls that must be flagged.

Phase 3: covers every adversary named in the final theorems (`Reduction/HeadlineFinal.lean`,
`Reduction/TcrMemoHeadline.lean`, `Reduction/Linear*.lean`, `E2E/Headline.lean`).
-/

partial def reach (env : Environment) (n : Name) (seen : NameSet) : NameSet := Id.run do
  if seen.contains n then return seen
  let mut seen := seen.insert n
  match env.find? n with
  | some (.defnInfo d) =>
    for c in d.value.getUsedConstants do seen := reach env c seen
    return seen
  | some (.opaqueInfo _) => return seen
  | _ => return seen

elab "#final_check " ids:ident+ : command => do
  let env ← getEnv
  let bad : List Name := [`Reduction.sampleTable, `Reduction.Tables.uniformTable,
    `Reduction.Tables.UniformSampler.sample, `Fintype.mPi, `Classical.choice, `Fin.mOfFn,
    `Classical.indefiniteDescription, `Exists.choose, `Fintype.equivFin,
    `Classical.propDecidable]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let s := reach env n {}
    let hits := bad.filter s.contains
    logInfo m!"{n}: {s.size} constants; flagged: {hits}"

-- the twelve adversaries of the final bounds (EUF and SUF variants of the first two)
#final_check Reduction.bPrfC Reduction.bPrfWC Reduction.sufCheck Reduction.Lazy.bPrfMsgL
  Reduction.Lazy.bPrfMsgWL Reduction.Lazy.bItsrL Reduction.Lazy.bOpenPreS Reduction.toDspr
  Reduction.toTcr Reduction.bTcrArM Reduction.Lazy.bWotsS Reduction.rUd Reduction.rPre
  Reduction.rTcrT
-- parts of the class adversaries `bTcrArM` (phase 1 = `route` over `bTcrS.choose`; phase 2 =
-- `memoForge`) and of the re-capping
#final_check Reduction.memoForge Reduction.findCollisionM Reduction.chkM Reduction.classOut
  Reduction.Lazy.bTcrS Reduction.TcrSplit.route Reduction.TcrSplit.routeStep
  Reduction.TcrSplit.classIdx Reduction.arityDefault Reduction.TightCaps.retype
  Reduction.TightCaps.recap Reduction.rTcr
-- wrappers: external interface, byte level
#final_check Reduction.toInternal Reduction.toInternalS Reduction.Guarded.reduce
  Reduction.Guarded.reduceS Reduction.pureEncode
#final_check Reduction.bytesToTyped Reduction.bytesToTypedS Reduction.pureBytesToTyped
  Reduction.pureBytesToTypedS Reduction.Coded.reduce Reduction.Coded.reduceS
  Reduction.Coded.signingImpl Reduction.Coded.readForgery Reduction.bytesView
  Reduction.pureBytesView Reduction.codec128s
-- the byte-level cores (the functions the Rust code computes)
#final_check Reduction.byteKeygen Reduction.byteSign Reduction.byteVerify Reduction.byteSignPure
  Reduction.byteVerifyPure
-- open programs of the resource statements
#final_check Reduction.Resources2.memoForgeOpen Reduction.Resources2.collO
  Reduction.Resources2.verifyFree Reduction.Resources2.findOpenFull
  Reduction.Resources2.wotsPhase2O
-- superseded adversaries still named in older theorems (also clean)
#final_check Reduction.bTcrArS Reduction.bTcrArST Reduction.TcrSplit.restrict
-- controls (must be flagged): the eager phase-1 adversaries, and bounds (advantages are measures)
#final_check Reduction.bPrfMsg Reduction.bPrfMsgW Reduction.bTcr Reduction.bTcrAr
  Reduction.betaSufFinal Reduction.betaSufFinalSplit Reduction.betaSufFinalMemo
  Reduction.linRealSuf
