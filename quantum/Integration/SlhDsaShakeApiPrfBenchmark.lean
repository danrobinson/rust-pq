import Integration.SlhDsaShakeApiSkBound
import Integration.SlhDsaShakeApiMsgBridge

namespace Reduction.ShakeApi
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives

theorem prf_budgets (S : Sha2Set) :
    Sk.budget S (2^40) 1 ≤ 2^41 ∧ Msg.budget S (2^40) 1 ≤ 2^41 := by
  cases S <;> decide

noncomputable def prfLoss (S : Sha2Set) := ENNReal.ofReal (8 * ((2:ℝ)^41)^2 / 2^(8*S.vp.params.n))

private theorem loss_mono (S : Sha2Set) {q : ℕ} (hq : q ≤ 2^41) :
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) ≤ prfLoss S := by
  have h : (q : ℝ) ≤ 2^41 := by exact_mod_cast hq
  apply ENNReal.ofReal_le_ofReal
  gcongr

variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)

theorem secret_prf_benchmark (cap : 2*S.vp.params.n+32 ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    let A := fun H : RawTable S N => qbPrfWC sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (skPrfC S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) + prfLoss S :=
  (Sk.real_le_ideal S N rand seeds F cap _ _ hq hs).trans (add_le_add le_rfl (loss_mono S (prf_budgets S).1))

theorem message_prf_benchmark (c : Caps) (cap : 2*S.vp.params.n+c.ml ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let A := fun H : RawTable S N => qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (msgPrf S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) + prfLoss S :=
  (Msg.real_le_ideal S N rand seeds F c cap _ _ hq hs hc).trans (add_le_add le_rfl (loss_mono S (prf_budgets S).2))

end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.prf_budgets
#print axioms Reduction.ShakeApi.secret_prf_benchmark
#print axioms Reduction.ShakeApi.message_prf_benchmark
