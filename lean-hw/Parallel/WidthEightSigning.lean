import Parallel.WidthEightSome
import Parallel.PhaseTwoObserved
import Shakebatch.WidthEightSession
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.ParallelSign
open ParallelCaller ParallelSignJoin
noncomputable section

structure Config where
  host : Platform
  threads : Usize
  schedule : ∀ n, Ticket.Schedule n

@[instance_reducible] def fallback (h : Platform) : Sh.Fallback where
  forsSign := @WidthEight.forsSign h
  forsRecover := @WidthEight.forsRecover h
  htSign := @WidthEight.htSign h

theorem fallback_correct (h : Platform) {N : Usize} (p : params.Params) (hp : PN p N) :
    Sh.FallbackCorrect (fallback h) (N:=N) p :=
  ⟨WidthEight.forsSign_spec h p hp,WidthEight.forsRecoverSpec h p hp,WidthEight.htSignSpec h p hp⟩

def joinedPlan (host : Platform) (schedule : ∀ n, Ticket.Schedule n) (plan : PhysicalRows) : Join :=
  Ticket.completedJoin host (Ticket.rootsFrom host (Ticket.observedInputs plan schedule))

theorem computed_correct (host : Platform) (schedule : ∀ n, Ticket.Schedule n) (threads : Usize)
    {N : Usize} (p : params.Params) (hp : PN p N) :
    WorkerCorrect (replayWith (joinedPlan host schedule) threads) (N:=N) p (Shake.params p)
      (fun s => bytes s.val) (fun _ => True) := by
  intro md sk seed a r tree leaf seedOk mdLen treeLt leafLt address
  dsimp only [replayWith,Worker.run]
  cases found : lookup (Shake.params p) with
  | none => simp [found]
  | some plan =>
    try simp only [found]
    exact worker_correct threads _ p hp
      (Ticket.joined_from_forest host _ p hp (Ticket.observed_law schedule p hp plan found))
      md sk seed a r tree leaf seedOk mdLen treeLt leafLt address

theorem worker_returns (c : Config) (enabled : 2≤c.threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32)
    (mdLen : md.length=(Shake.params p).mdBytes) (treeLt : tree.val<2^(p.h.val-p.hp.val))
    (leafLt : leaf.val<2^p.hp.val) (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
      Spec.FORS_TREE with keypair:=leaf.val}) :
    ∃ sig, ((replayWith (joinedPlan c.host c.schedule) c.threads).run p md sk seed a r tree leaf)=ok (some sig) ∧
      bytes sig.val=bytes r.val ++ Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) ++
      Spec.htSign (Shake.params p) (Spec.forsPkFromSig (Shake.params p) (Spec.forsSign (Shake.params p)
        (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)) (bytes md.val) (bytes seed.val) (adrsS a))
        (bytes sk.val) (bytes seed.val) tree.val leaf.val := by
  obtain ⟨plan,found⟩ := rust_supported p member
  let join : Join := joinedPlan c.host c.schedule plan
  have law : JoinLawAt join N p := Ticket.joined_from_forest c.host _ p hp
    (Ticket.observed_law c.schedule p hp plan found)
  obtain ⟨ret,eq,value⟩ := spec_imp_exists
    (result c.threads join p hp law md sk seed a r tree leaf mdLen treeLt leafLt address)
  cases ret with
  | none =>
    change c.threads < 2#usize ∨ p.hp=0#u32 at value
    have pos := hp.valid.hp_pos
    change 0<p.hp.val at pos
    rcases value with low|empty
    · scalar_tac
    · rw [empty] at pos;contradiction
  | some sig =>
    refine ⟨sig,?_,ParallelFused.Slots.output_fips _ (Suite.valid .shake hp) _ _ _ _ _ _ _ _ leafLt value⟩
    dsimp only [replayWith,Worker.run]
    rw [found]
    exact eq

abbrev internal (c : Config) := @Sh.shake.slh.slh_sign_internal (fallback c.host) (replayWith (joinedPlan c.host c.schedule) c.threads)
abbrev context (c : Config) := @Sh.shake.slh.shake_sign_ctx (fallback c.host) (replayWith (joinedPlan c.host c.schedule) c.threads)

theorem internal_spec (c : Config) {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) :
    internal c p m sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
      (bytes m.val) (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @Sh.sign_spec (fallback c.host) (replayWith (joinedPlan c.host c.schedule) c.threads) N p hp m sk rnd hsk (fallback_correct c.host p hp)
    (computed_correct c.host c.schedule c.threads p hp)

theorem context_spec (c : Config) {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (hsk : sk.length=4*N.val) (hc : ctx.length≤255) :
    context c p m ctx sk rnd ⦃ out => bytes out.val=Spec.slhSignInternal (Shake.params p)
      (Spec.withContext (bytes m.val) (bytes ctx.val)) (bytes sk.val) (bytes rnd.val) ∧ out.length=(paramsS p).sigBytes ⦄ :=
  @Sh.sign_ctx_spec (fallback c.host) (replayWith (joinedPlan c.host c.schedule) c.threads) N p hp m ctx sk rnd hsk hc
    (fallback_correct c.host p hp) (computed_correct c.host c.schedule c.threads p hp)

theorem internal_uses_worker (c : Config) (enabled : 2≤c.threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets) (other : Sh.Fallback)
    (m sk : Slice U8) (rnd : Array U8 N) :
    internal c p m sk rnd = @Sh.shake.slh.slh_sign_internal other (replayWith (joinedPlan c.host c.schedule) c.threads) N p m sk rnd :=
  fallback_irrelevant (joinedPlan c.host c.schedule) c.threads enabled p hp member _ other m sk rnd _ _

theorem context_uses_worker (c : Config) (enabled : 2≤c.threads.val) {N : Usize}
    (p : params.Params) (hp : PN p N) (member : p ∈ rustSets) (other : Sh.Fallback)
    (m ctx sk : Slice U8) (rnd : Array U8 N) :
    context c p m ctx sk rnd = @Sh.shake.slh.shake_sign_ctx other (replayWith (joinedPlan c.host c.schedule) c.threads) N p m ctx sk rnd :=
  fallback_irrelevant (joinedPlan c.host c.schedule) c.threads enabled p hp member _ other m sk rnd _ _

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let names ← IO.mkRef (Std.HashMap.ofList [
    (`slhdsa.shake.slh.slh_sign_internal,`slhdsa.WidthEight.ParallelSign.internal),
    (`slhdsa.Shake.slh_sign_internal_all_lengths,`slhdsa.WidthEight.ParallelSign.internal_spec),
    (`ShakeoptSeg.shake.slh.shake_sign_ctx,`slhdsa.WidthEight.ParallelSign.context),
    (`Shakeopt.Segmented.shake_sign_ctx_spec,`slhdsa.WidthEight.ParallelSign.context_spec)])
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do
      let base := `slhdsa ++ setName ++ op
      let goal := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthEightParallel [`Slhdsa,`Shakebatch,`Shakeopt]
        goal names `slhdsa.WidthEight.ParallelSign.Config
      unless actual == `WidthEightParallel ++ goal do throwError "missing public parallel signer {goal}"

end
end slhdsa.WidthEight.ParallelSign
