import Integration.SlhDsaShakePermutationMsgCalls

namespace Reduction.ShakePermutation.MsgSplit
open Classical MLink SLHDSA SLHDSA.Security OracleSpec OracleComp PQ.Interactive Quantum ENNReal SetOracle
variable {W D R A : Type} [Fintype W] [Inhabited R]
variable [DecidableEq D] [SampleableType R]

noncomputable def resumeFresh : Stage W D R A → Closed W A
  | .inl a => pure a
  | .inr (_,post) => liftU ($ᵗ R) >>= post

private theorem idle_ideal (p : Source W D R A) (bound : CountBound (fun i => isChallenge i = true) p 0)
    (c : (D →ₒ R).QueryCache) : idealRun p c = ansRun (fun _ => default) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rw [idealRun_pure,ansRun_pure]
  | query_bind t k ih =>
    rw [countBound_query_bind] at bound
    rcases t with j | (n|d)
    · rw [idealRun_instr,ansRun_instr]; exact bind_congr fun r => ih r (bound r)
    · rw [idealRun_unif,ansRun_unif]; exact bind_congr fun r => ih r (bound r)
    · simp [isChallenge] at bound

theorem fresh (p : Source W D R A) (bound : CountBound (fun i => isChallenge i = true) p 1) :
    idealRun p ∅ = before p >>= resumeFresh := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [before,resumeFresh,idealRun_pure]
  | query_bind t k ih =>
    rw [countBound_query_bind] at bound
    rcases t with j | (n|d)
    · rw [idealRun_instr]
      change _ = (liftM ((instrSpec W + unifSpec).query (.inl j)) >>= fun r => before (k r)) >>= _
      rw [bind_assoc]
      exact bind_congr fun r => ih r (bound r)
    · rw [idealRun_unif]
      change _ = (liftM ((instrSpec W + unifSpec).query (.inr n)) >>= fun r => before (k r)) >>= _
      rw [bind_assoc]
      exact bind_congr fun r => ih r (bound r)
    · rw [idealRun_oracle_none _ _ _ rfl]
      change _ = pure (.inr (d,fun r => ansRun (fun _ => default) (k r)) : Stage W D R A) >>= _
      rw [pure_bind]
      exact bind_congr fun r => idle_ideal (k r) (bound.2 r) _

/-- Any independent uniform table used only by the continuation can be
sampled after the measured data from the quantum prefix are available. -/
theorem defer_uniform {T Z V : Type} [Fintype T] [DecidableEq T] [SampleableType T]
    (prefixP : Closed W Z) (post : T → Z → Closed W V) (event : V → Prop) [DecidablePred event]
    (M : Matrix W W ℂ) :
    uniformMean (fun t => qWeight event (prefixP >>= post t) M) =
      qWeight event (prefixP >>= fun z => liftU ($ᵗ T) >>= fun t => post t z) M := by
  induction prefixP using OracleComp.inductionOn generalizing M with
  | pure a =>
    simp only [pure_bind,qWeight_liftU_uniform_bind,uniformMean,unifW,Finset.mul_sum]
  | query_bind i k ih =>
    simp only [bind_assoc]
    rcases i with j|n
    · simp only [qWeight_instr_bind,uniformMean,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      exact ih u _
    · simp only [qWeight_unif_bind,uniformMean]
      conv_lhs => arg 2; intro t; rw [mul_left_comm]
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => ih u M

section Native
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (base : ShakeApi.Xof S) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
    (port : Port → Words)
local notation "P₀" => ShakeApi.primitives S base
local notation "Work" => WS Port Words E
local notation "P" => qbPrfMsgWL sufCheck (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F base port))

theorem native_ideal (hs : ∀ pk, CountBound isSign (F.main pk) 1) (M : Matrix Work Work ℂ) :
    qPrfIdealPr P M = qWeight (· = true) (before P >>= resumeFresh) M :=
  congrArg (fun p => qWeight (· = true) p M) (fresh P (native_count S base F rand seeds port 1 hs))

theorem native_real (hs : ∀ pk, CountBound isSign (F.main pk) 1) (M : Matrix Work Work ℂ) :
    qPrfRealPr (msgPrf S.vp P₀) P M = qWeight (· = true)
      (before P >>= fun z => liftU ($ᵗ S.Node) >>= fun k => resume (fun d => (P₀).PRFmsg k d.1 d.2) z) M := by
  let value (k : S.Node) (d : S.Node × List SLHDSA.Byte) := (P₀).PRFmsg k d.1 d.2
  have run (k) := answered (value k) P (native_count S base F rand seeds port 1 hs)
  unfold qPrfRealPr qPrfRealExperiment
  change qWeight (· = true) (liftU ($ᵗ S.Node) >>= fun k => ansRun (value k) P) M = _
  rw [qWeight_liftU_uniform_bind]
  simp only [run]
  simpa only [uniformMean,unifW,Finset.mul_sum] using
    defer_uniform (before P) (fun k => resume (value k)) (· = true) M
end Native
end Reduction.ShakePermutation.MsgSplit
#print axioms Reduction.ShakePermutation.MsgSplit.native_real
#print axioms Reduction.ShakePermutation.MsgSplit.native_ideal
