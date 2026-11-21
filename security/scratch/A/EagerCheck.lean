import Reduction.FinalV2
open Lean Elab Command

/-- Constants reachable through definition BODIES (theorem proofs are not followed; types of
theorems are not followed either). -/
partial def reach (env : Environment) (n : Name) (seen : NameSet) : NameSet := Id.run do
  if seen.contains n then return seen
  let mut seen := seen.insert n
  match env.find? n with
  | some (.defnInfo d) =>
    for c in d.value.getUsedConstants do seen := reach env c seen
    return seen
  | some (.opaqueInfo _) => return seen
  | _ => return seen

elab "#eager_check " ids:ident+ : command => do
  let env ← getEnv
  let bad : List Name := [`Reduction.sampleTable, `Reduction.Tables.uniformTable,
    `Reduction.Tables.UniformSampler.sample, `Fintype.mPi, `Classical.choice, `Fin.mOfFn,
    `Classical.indefiniteDescription, `Exists.choose, `Fintype.equivFin]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let s := reach env n {}
    let hits := bad.filter s.contains
    logInfo m!"{n}: {s.size} constants; flagged: {hits}"

#eager_check Reduction.bPrfC Reduction.Lazy.bPrfMsgL Reduction.Lazy.bItsrL Reduction.Lazy.bOpenPreS Reduction.Lazy.bTcrS Reduction.Lazy.bWotsS Reduction.betaV2 Reduction.bPrfMsg Reduction.rUd Reduction.rPre Reduction.rTcr
