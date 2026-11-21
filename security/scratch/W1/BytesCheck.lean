import Reduction.Headline
import Reduction.HeadlineSplit
import Reduction.Bytes
open Lean Elab Command

/-!
Definition-level check for package W1 (byte-level transfer) (not part of the build; run with
`lake env lean scratch/W1/BytesCheck.lean`).

For each named constant it follows definition BODIES transitively (never theorem proofs, never
the types of theorems) and reports which of the following constants are reached:
choice principles (`Classical.choice`, `Classical.indefiniteDescription`, `Exists.choose`,
`Classical.propDecidable`, `Fintype.equivFin`) and eager objects (`Reduction.sampleTable`,
`Reduction.Tables.uniformTable`, `Reduction.Tables.UniformSampler.sample`, `Fin.mOfFn`,
`Fintype.mPi`).  The last three lines are controls that must be flagged.
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

elab "#w1_check " ids:ident+ : command => do
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

-- the byte-level wrappers and the cores of the byte-level schemes
#w1_check Reduction.bytesToTyped Reduction.bytesToTypedS Reduction.pureBytesToTyped
  Reduction.pureBytesToTypedS Reduction.Coded.reduce Reduction.Coded.reduceS
  Reduction.Coded.signingImpl Reduction.Coded.readForgery Reduction.bytesView
  Reduction.pureBytesView Reduction.byteKeygen Reduction.byteSign Reduction.byteVerify
  Reduction.byteSignPure Reduction.byteVerifyPure Reduction.codec128s
-- control (must be flagged)
#w1_check Reduction.betaSufFinalSplit
