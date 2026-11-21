import Reduction
import E2E
open Lean Elab Command

/-!
Definition-level check for the general-spec (GEN) adversaries; same checker as scratch/Final/FinalCheck.lean, (not part of the build; run with
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

elab "#gen_check " ids:ident+ : command => do
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

-- the reduction adversaries around a general-spec forger family (EUF and SUF variants)
#gen_check Reduction.Gen.bPrfCG Reduction.Gen.bPrfWCG Reduction.Gen.bPrfMsgLG
  Reduction.Gen.bPrfMsgWLG Reduction.Gen.bItsrLG Reduction.Gen.toDsprG Reduction.Gen.toTcrG
  Reduction.Gen.bTcrArMG Reduction.Gen.rUdG Reduction.Gen.rPreG Reduction.Gen.rTcrTG
-- their parts
#gen_check Reduction.Gen.bPrfG Reduction.Gen.bPrfWG Reduction.Gen.openAdv Reduction.Gen.msgOpenG
  Reduction.Gen.msgOpenWG Reduction.Gen.itsrOpenG Reduction.Gen.lazyRunG
  Reduction.Gen.findOpenPreG Reduction.Gen.forgeOpenPreG Reduction.Gen.guessOpenPreG
  Reduction.Gen.chooseOpenPreTcr Reduction.Gen.chooseOpenPreDspr Reduction.Gen.memoForgeG
  Reduction.Gen.chooseArM Reduction.Gen.g2RunG Reduction.Gen.g2RunWithG
  Reduction.Gen.bWotsForgeG Reduction.Gen.udPickW Reduction.Gen.preChooseW
  Reduction.Gen.tcrChooseW Reduction.Gen.dummyForger
-- the toolkit that runs the forger
#gen_check Reduction.Gen.liftR Reduction.Gen.embed Reduction.Gen.gImplT Reduction.Gen.gImpl
  Reduction.Gen.gImplO Reduction.Gen.gImplS Reduction.Gen.runG Reduction.Gen.runGO
  Reduction.Gen.wrapS Reduction.Gen.wrapFam Reduction.Gen.compS Reduction.Gen.compST
  Reduction.Gen.compSS Reduction.Gen.idW Reduction.Gen.stOf Reduction.Gen.liftAlg
  Reduction.Gen.signH
-- wrappers and embeddings
#gen_check Reduction.Gen.toInternalG Reduction.Gen.toInternalSG Reduction.Gen.bytesToTypedG
  Reduction.Gen.bytesToTypedSG Reduction.Gen.pureBytesToTypedG Reduction.Gen.pureBytesToTypedSG
  Reduction.Gen.embedAdv Reduction.Gen.embedAdvS Reduction.Gen.SM_DT_TCR_AdversaryG.ofClassical
  Reduction.Gen.SM_DT_UD_AdversaryG.ofClassical Reduction.Gen.SM_DT_PRE_AdversaryG.ofClassical
  Reduction.Gen.DsprFVAdversaryG.ofClassical Reduction.Gen.TcrFVAdversaryG.ofClassical
  Reduction.Gen.ITSRAdversaryG.ofClassical
-- wrapper-game experiments (programs; their values are measures)
#gen_check Reduction.Gen.prfRealExperimentG Reduction.Gen.prfIdealExperimentG
  Reduction.Gen.ITSRExperimentG Reduction.Gen.SM_DT_TCR_ExperimentG
  Reduction.Gen.SM_DT_UD_ExperimentG Reduction.Gen.SM_DT_PRE_ExperimentG
  Reduction.Gen.dsprExperimentG Reduction.Gen.dsprSPExperimentG Reduction.Gen.tcrFVExperimentG
  Reduction.Gen.sigExpG
-- open programs of the resource statements
#gen_check Reduction.Gen.memoForgeOpenG Reduction.Gen.findOpenFullG Reduction.Gen.wotsPhase2OG
-- controls (must be flagged): values/bounds are measures
#gen_check Reduction.Gen.prG Reduction.Gen.betaSufG Reduction.Gen.linRealSufG
  Reduction.Gen.SM_DT_TCR_AdvantageG Reduction.Gen.eufAdvG
