import Integration.SlhDsaShakeAdaptiveMachine
import Integration.SlhDsaCompressionPrfSample

namespace Reduction.ShakeAdaptive
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum QMsg QItsr KeyedHash

set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeApi.primitives ShakeSecurity.primitives

private theorem lazy_draw {W D V α K ι κ : Type} [Fintype W] [DecidableEq D] [SampleableType V]
    {G : OracleSpec ι} {hs : OracleSpec κ} (h : QueryImpl hs Id) (seeds : ProbComp K)
    (next : K → QOC W (Lazy.RSpec G D V hs) α) :
    qLazyRun h (liftQ (liftM seeds : OracleComp _ K) >>= next) =
      liftQ (liftM seeds : OracleComp (unifSpec + G) K) >>= fun k => qLazyRun h (next k) := by
  induction seeds using OracleComp.inductionOn with
  | pure k => simp
  | query_bind n f ih =>
    simp only [liftM_bind,liftQ_bind,bind_assoc]
    change qLazyRun h (liftM ((instrSpec W + Lazy.RSpec G D V hs).query (.inr (.inl n))) >>= _) =
      liftM ((instrSpec W + (unifSpec + G)).query (.inr (.inl n))) >>= _
    unfold qLazyRun
    rw [wrap_query_bind,map_bind]
    rw [forwardsUnifB_lazyImplR n []]
    simp only [liftQ,simulateQ_map,bind_map_left]
    change wrap0 _ (liftM ((instrSpec W + Lazy.RSpec G Unit V hs).query (.inr (.inl n))) >>= _) = _
    rw [wrap0_query_bind]
    exact bind_congr ih

/-- An arbitrary independent public-seed sampler mixes the actual signature
reduction's fixed-seed ITSR advantages with the sampler's exact probabilities. -/
theorem itsr_seed_average (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
    (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E) (H : ShakeApi.RawTable S N) :
    let risk := fun (dist : ProbComp S.Node) =>
      let A := qPureBytesToInternal (ShakeApi.rawForger S N rand dist F H)
      qItsrAdvantage (itsrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend H))) (qbItsrL A) F.ρ₀
    risk seeds = ∑' seed, prob seeds (· = seed) * risk (pure seed) := by
  dsimp only
  unfold qbItsrL qItsrOpen
  set_option backward.isDefEq.respectTransparency false in
    rw [lazy_draw (D := SecIdx) (V := S.Node)]
  simp only [liftM_pure,liftQ_pure,pure_bind]
  unfold qItsrAdvantage
  let problem := itsrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend H))
  have factor := @Compression.close_draw (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) _ _ (S.Node × ItsrIn (ShakeApi.primitives S (ShakeApi.extend H))) _ _ _
    (ITSROracles problem) (forwardsUnif_ofLift_add _) seeds
  unfold Compression.drawThen at factor
  rw [factor,qWeight_liftU_bind_tsum]
  rfl

end Reduction.ShakeAdaptive
#print axioms Reduction.ShakeAdaptive.itsr_seed_average
