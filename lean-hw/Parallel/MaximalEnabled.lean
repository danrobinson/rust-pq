import Parallel.MaximalPublic
open Lean Elab Command Meta
open slhdsa.MaximalWorker

namespace slhdsa.MaximalWorker
open ParallelFused ParallelSigning ParallelCached

/-- At the last phase-one increment, each physical publication precedes both
reduction and every participant's acquire of the layer roots. -/
theorem Session.publication {f x l w} (s : Session f x l w) :
    ∃ done, LastFinisher.History s.plan.jobs s.plan.jobs.length [] done s.first.state.cells ∧
    done.length=s.plan.jobs.length ∧
    ∀ t c (valid : t<s.plan.jobs.length), (c,())∈s.plan.jobs[t] → ∀ reader : Nat,
      let owns := fun j k => ∃ v, (k,v)∈Tickets.writes s.plan.jobs j
      Publication.Before done.reverse owns (.slot t c) .reduce ∧
      Publication.Before done.reverse owns (.slot t c) (.readRoots reader) := by
  obtain ⟨done,h,last⟩ := last_finisher (s.first.project s.plan.chunkLayout) s.plan.jobs (.refl _)
  exact ⟨done,h,last,fun _ _ valid entry reader => LastFinisher.visibility h last valid entry reader⟩

end slhdsa.MaximalWorker

/- Check the enabled worker itself: it returns Some with the complete FIPS
signature before the public caller can choose its serial continuation. -/
set_option Elab.async false in
run_cmd liftTermElabM do
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    let p := mkConst (`slhdsa.sets ++ suite ++ `params.PARAMS)
    let hp := mkConst (`slhdsa ++ suite ++ `pn)
    for src in [`ParallelAppleAPI,`ParallelX86API,`ParallelLinuxArmAPI] do
      for fromPrefix in [false,true] do
        let finish (args : Array Expr) : MetaM Unit := do
          let domain := mkApp (mkConst (if fromPrefix then ``StartFor else ``For)) p
          withLocalDeclD (if fromPrefix then `prefixes else `histories) domain fun hist =>
            withLocalDeclD `threads (mkConst `Aeneas.Std.Usize) fun threads => do
              let session ← if fromPrefix then mkAppM ``Beginning.complete #[hist] else pure hist
              let sched ← mkAppM ``Session.schedules #[session]
              let partialProof ← if src == `ParallelLinuxArmAPI then
                pure (mkAppN (mkConst `slhdsa.ParallelSignJoin.enabled_bytes) #[sched,threads])
              else do
                let apple := src == `ParallelAppleAPI
                let host := if apple then mkApp (mkConst `slhdsa.WidthEight.Platform.apple) args[0]! else mkConst `slhdsa.WidthEight.Platform.x86
                let config ← mkAppM `slhdsa.WidthEight.ParallelSign.Config.mk #[host,threads,sched]
                let root := (if apple then `ParallelApple else `ParallelX86) ++ `slhdsa.WidthEight.ParallelSign.worker_returns
                pure (mkApp (mkConst root) config)
              forallBoundedTelescope (← inferType partialProof) (some 1) fun enabled _ => do
                let fn := mkApp partialProof enabled[0]!
                let implicitWidth ← mkFreshExprMVar (mkConst `Aeneas.Std.Usize)
                let body := mkAppN fn #[implicitWidth,p,hp]
                check body
                let val ← mkLambdaFVars (((args.push hist).push threads)++enabled) (←instantiateMVars body)
                let dst := (if fromPrefix then `PrefixSigning else `MaximalSigning) ++ src ++ suite ++ `worker_returns
                addDecl <| .thmDecl {«name» := dst,levelParams := [],type := ←inferType val,value := val}
        if src == `ParallelAppleAPI then withLocalDeclD `sha3 (mkConst `Bool) fun flag => finish #[flag]
        else finish #[]
