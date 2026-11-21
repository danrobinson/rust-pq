import Reduction.TcrMemoHeadline
open Lean Elab Command

/-!
Definition-level check for package W5 (not part of the build; run with
`lake env lean scratch/W5/MemoCheck.lean`).  Same checker as `scratch/Final/FinalCheck.lean`:
for each named constant it follows definition BODIES transitively (never theorem proofs, never
the types of theorems) and reports which choice principles / eager objects are reached.
The last line is a control that must be flagged.
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

-- the memoising class adversaries and their parts
#final_check Reduction.bTcrArM Reduction.memoForge Reduction.findCollisionM Reduction.chkM
  Reduction.classOut
-- the open phase-2 program and its parts
#final_check Reduction.Resources2.memoForgeOpen Reduction.Resources2.collO
  Reduction.Resources2.hashQ Reduction.Resources2.verifyFree Reduction.Resources2.thQ
-- controls (must be flagged): the eager adversary, and a bound (advantages are measures)
#final_check Reduction.bTcrAr Reduction.betaEufFinalMemo
