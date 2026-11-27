import Parallel.WorkerFetch
import Parallel.MaximalCoverage

open Lean Elab Command Meta
open slhdsa.MaximalWorker

namespace slhdsa.WorkerFetch

structure SigningRuns (p : params.Params) where
  plan : PhasePlan (p.k.val*(p.a.val+1))
    (ParallelRawChunks.slots p.hp.val (p.d.val*p.hp.val)).length (p.d.val-1)
  workers : Nat
  positive : 0<workers
  phaseOne : Joined plan.jobs workers
  phaseTwo : Joined (single p.d.val).jobs workers

def SigningRuns.toSession {p} (runs : SigningRuns p) : For p :=
  session runs.plan runs.positive runs.phaseOne runs.phaseTwo

theorem signing_from_prefixes {p : params.Params} (plan : PhasePlan (p.k.val*(p.a.val+1))
    (ParallelRawChunks.slots p.hp.val (p.d.val*p.hp.val)).length (p.d.val-1))
    {workers m₁ m₂ log₁ log₂} (positive : 0<workers)
    (one : Execution plan.jobs workers m₁ log₁) (two : Execution (single p.d.val).jobs workers m₂ log₂)
    (fits₁ : plan.jobs.length+workers < 2^Aeneas.Std.UScalarTy.Usize.numBits)
    (fits₂ : (single p.d.val).jobs.length+workers < 2^Aeneas.Std.UScalarTy.Usize.numBits) :
    ∃ runs : SigningRuns p, runs.plan=plan ∧ runs.workers=workers ∧
      log₁ <:+ runs.phaseOne.log ∧ log₂ <:+ runs.phaseTwo.log := by
  obtain ⟨a,pastA,_⟩ := joins_from_prefix one plan.unique fits₁
  obtain ⟨b,pastB,_⟩ := joins_from_prefix two (single p.d.val).unique fits₂
  exact ⟨⟨plan,workers,positive,a,b⟩,rfl,rfl,pastA,pastB⟩

end slhdsa.WorkerFetch

/- Specialize the checked public API results to two shared-state queue runs.
The resulting theorem statements retain the actual signer and its native calls. -/
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    let p := mkConst (`slhdsa.sets ++ suite ++ `params.PARAMS)
    for host in [`ParallelAppleAPI,`ParallelX86API,`ParallelLinuxArmAPI] do
      let publish (args : Array Expr) : MetaM Unit := do
        withLocalDeclD `runs (mkApp (mkConst ``slhdsa.WorkerFetch.SigningRuns) p) fun runs => do
          let session ← mkAppM ``slhdsa.WorkerFetch.SigningRuns.toSession #[runs]
          for op in [`roundtrip,`worker_returns] do
            let proof := mkApp (mkAppN (mkConst (`MaximalSigning ++ host ++ suite ++ op)) args) session
            let val ← mkLambdaFVars (args.push runs) proof
            let dst := `WorkerFetchSigning ++ host ++ suite ++ op
            addDecl <| .thmDecl {«name» := dst, levelParams := [], type := ← inferType val, value := val}
      if host == `ParallelAppleAPI then withLocalDeclD `sha3 (mkConst ``Bool) fun flag => publish #[flag]
      else publish #[]
