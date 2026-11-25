import Parallel.PhaseTwoLinux
import Parallel.KeygenWidthThreeRoundTrip
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelSignJoin
noncomputable section

abbrev TicketSchedule := ∀ n, WidthEight.Ticket.Schedule n

def linuxJoin (schedule : TicketSchedule) (plan : PhysicalRows) : Join :=
  ThreeLane.slhdsa.WidthEight.Ticket.completedJoin .linuxArm
    (ThreeLane.slhdsa.WidthEight.Ticket.rootsFrom .linuxArm (WidthEight.Ticket.observedInputs plan schedule))

theorem linux_join_correct (schedule : TicketSchedule) {N : Usize} (p : params.Params) (hp : PN p N)
    (plan : PhysicalRows) (found : lookup (Shake.params p)=some plan) : JoinLawAt (linuxJoin schedule plan) N p :=
  ThreeLane.slhdsa.WidthEight.Ticket.joined_from_forest .linuxArm _ p hp
    (WidthEight.Ticket.observed_law schedule p hp plan found)

/-- Replay only the parameter shapes for which the symbolic Rust worker emitted
a physical-cell witness. The six standardized SHAKE profiles all have one. -/
@[instance_reducible] def replay (schedule : TicketSchedule) (threads : Usize) : ParallelCaller.Worker ParallelCaller.ShakeSeed where
  run p md sk seed a r tree leaf := match lookup (Shake.params p) with
    | none => ok none
    | some plan => run (ok threads) (linuxJoin schedule plan) p md sk seed a r tree leaf

def projectedPublished (schedule : TicketSchedule) (threads : Usize) : WidthThree.PublishedWorker where
  worker := replay schedule threads
  published p hp := by
    intro md sk seed a r tree leaf seedOk mdLen treeLt leafLt address
    dsimp only [replay,ParallelCaller.Worker.run]
    cases found : lookup (Shake.params p) with
    | none => simp [found]
    | some plan =>
      try simp only [found]
      exact worker_correct threads (linuxJoin schedule plan) p hp (linux_join_correct schedule p hp plan found)
        md sk seed a r tree leaf seedOk mdLen treeLt leafLt address

/-- An available pool returns a completed signature on every source-supported
shape. In particular the projection cannot establish the round trip by declining
all work. -/
theorem enabled_returns (schedule : TicketSchedule) (threads : Usize) (enabled : 2≤threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (plan : PhysicalRows) (found : lookup (Shake.params p)=some plan)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (mdLen : md.length=(Shake.params p).mdBytes) (treeLt : tree.val<2^(p.h.val-p.hp.val))
    (leafLt : leaf.val<2^p.hp.val) (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
      Spec.FORS_TREE with keypair:=leaf.val}) :
    ∃ signature, (replay schedule threads).run p md sk seed a r tree leaf=ok (some signature) ∧
      ParallelFused.Slots.Output (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
        (bytes r.val) tree.val leaf.val (bytes signature.val) := by
  obtain ⟨ret,eq,good⟩ := spec_imp_exists
    (result threads (linuxJoin schedule plan) p hp (linux_join_correct schedule p hp plan found)
      md sk seed a r tree leaf mdLen treeLt leafLt address)
  dsimp only [replay,ParallelCaller.Worker.run]
  rw [found]
  cases ret with
  | none =>
    change threads < 2#usize ∨ p.hp=0#u32 at good
    have h := hp.valid.hp_pos
    simp only [paramsS_hp] at h
    rcases good with bad|bad
    · scalar_tac
    · rw [bad] at h;contradiction
  | some v => exact ⟨v,eq,good⟩

theorem enabled_bytes (schedule : TicketSchedule) (threads : Usize) (enabled : 2≤threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (plan : PhysicalRows) (found : lookup (Shake.params p)=some plan)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (mdLen : md.length=(Shake.params p).mdBytes) (treeLt : tree.val<2^(p.h.val-p.hp.val))
    (leafLt : leaf.val<2^p.hp.val) (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
      Spec.FORS_TREE with keypair:=leaf.val}) :
    ∃ signature, (replay schedule threads).run p md sk seed a r tree leaf=ok (some signature) ∧
      bytes signature.val=bytes r.val ++ Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
        (bytes seed.val) (adrsS a) ++ Spec.htSign (Shake.params p)
        (Spec.forsPkFromSig (Shake.params p) (Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
          (bytes seed.val) (adrsS a)) (bytes md.val) (bytes seed.val) (adrsS a))
        (bytes sk.val) (bytes seed.val) tree.val leaf.val := by
  obtain ⟨sig,eq,published⟩ := enabled_returns schedule threads enabled p hp plan found md sk seed a r tree leaf
    mdLen treeLt leafLt address
  exact ⟨sig,eq,ParallelFused.Slots.output_fips _ (Suite.valid .shake hp) _ _ _ _ _ _ _ _ leafLt published⟩

def rustSets := [params.SHA2_128S,params.SHA2_128F,params.SHA2_192S,
  params.SHA2_192F,params.SHA2_256S,params.SHA2_256F]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rust_supported (p : params.Params) (member : p ∈ rustSets) :
    ∃ plan, lookup (Shake.params p)=some plan := by
  have good : rustSets.all (fun set => (lookup (Shake.params set)).isSome) = true := by
    simp only [rustSets,List.all_cons,List.all_nil,Shake.params,paramsS_128s,paramsS_128f,
      paramsS_192s,paramsS_192f,paramsS_256s,paramsS_256f]
    exact standard_lookup
  exact Option.isSome_iff_exists.mp (List.all_eq_true.mp good p member)

theorem roundtrip (schedule : TicketSchedule) (threads : Usize) (outcome : ParallelKeygenHost.PoolOutcome) {N : Usize}
    (p : params.Params) (hp : PN p N) (secret prf publicSeed : Array U8 N)
    (sk pk msg ctx : Slice U8) (rnd : Array U8 N) (ks : sk.length=4*N.val)
    (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    ParallelKeygenHost.linuxGenerateSignVerify threads.val outcome
      (WidthThreeParallel.ShakeoptSeg.shake.slh.slh_sign (WidthThree.linuxParallel (projectedPublished schedule threads)) p)
      p secret prf publicSeed sk pk msg ctx rnd = ok true :=
  ParallelKeygenHost.linux_narrow_parallel_sign_roundtrip (projectedPublished schedule threads) p hp threads.val outcome
    secret prf publicSeed sk pk msg ctx rnd ks ps hc

open Lean Meta Elab Command in
set_option Elab.async false in
run_cmd liftTermElabM do
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    withLocalDeclD `schedule (mkConst ``TicketSchedule) fun schedule =>
      withLocalDeclD `threads (mkConst `Aeneas.Std.Usize) fun threads => do
        let w ← mkAppM ``projectedPublished #[schedule,threads]
        let emit (op : Name) (proof : Expr) : MetaM Unit := do
          let value ← mkLambdaFVars #[schedule,threads] proof
          addDecl <| .thmDecl {«name» := `ParallelLinuxArmAPI ++ suite ++ op,levelParams := [],type := ← inferType value,value}
        for op in [`slh_sign_internal,`slh_sign,`sign,`sign_deterministic] do
          emit op (mkApp (mkConst (`slhdsa.WidthThree.LinuxWorker ++ suite ++ op)) w)
        let p := mkConst (`slhdsa.sets ++ suite ++ `params.PARAMS)
        let hp := mkConst (`slhdsa ++ suite ++ `pn)
        withLocalDeclD `pool (mkConst ``ParallelKeygenHost.PoolOutcome) fun pool => do
          let proof ← mkAppOptM ``roundtrip #[some schedule,some threads,some pool,none,some p,some hp]
          emit `roundtrip (← mkLambdaFVars #[pool] proof)

end
end slhdsa.ParallelSignJoin
