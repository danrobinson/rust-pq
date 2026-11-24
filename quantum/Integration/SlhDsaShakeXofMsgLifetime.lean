import Integration.SlhDsaShakeXofMsgOpenCost
import Integration.SlhDsaShakeXofSkLifetime

namespace Reduction.ShakeApi.Msg.Mixed
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker ComplexOrder
set_option exponentiation.threshold 2048

theorem real_le_ideal (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E) (c : Caps)
    (cap : 2*S.vp.params.n+c.ml ≤ N) (q s : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let A := fun H : RawTable S N => qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (msgPrf S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) + ShakeXof.mixedPrfLoss S q (Msg.budget S 0 s) := by
  intro A
  let short := fun H => wrap0 (Restrict.restrictImpl (SetOracle.restrictMessage S c)) (A H)
  have games := Msg.capped_games S N rand seeds F c hcap
  have hr (H) := (games H).1
  have hi (H) := (games H).2
  change ∀ H, qPrfRealPr (msgPrf S.vp (primitives S (extend H))) (A H) F.ρ₀ =
    qPrfRealPr (ShakeXof.boundedMsgScheme S H) (short H) F.ρ₀ at hr
  change ∀ H, qPrfIdealPr (A H) F.ρ₀ = qPrfIdealPr (short H) F.ρ₀ at hi
  simp_rw [hr,hi]
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input N × Bytes S.vp.params.m) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  have unit : ρ.matrix.trace = 1 := by simpa [hρ,Matrix.trace_kronecker] using F.trace_eq_one
  rw [hρ]
  exact ShakeXof.mixed_msg_prf S cap short (machine S N rand seeds F c) q (Msg.budget S 0 s)
    (represented S N rand seeds F c) (fun a => public_cost S N rand seeds F c a q hq)
    (fun a => read_cost S N rand seeds F c a s hs) ρ unit

/-- Full-lifetime comparison for the message PRF of the actual signature
reduction. The signing oracle and the forger see the same raw XOF. -/
theorem signature_lifetime (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E) (c : Caps)
    (cap : 2*S.vp.params.n+c.ml ≤ N) (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) (2^64)) (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let A := fun H : RawTable S N => qbPrfMsgWL sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (msgPrf S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) + ((2:ℝ≥0∞)^Sk.Mixed.lifetimePrfBits S)⁻¹ :=
  (real_le_ideal S N rand seeds F c cap _ _ hq hs hcap).trans
    (add_le_add le_rfl (Sk.Mixed.lifetime_prf_loss S _ (Nat.le_max_right ..)))

end Reduction.ShakeApi.Msg.Mixed
#print axioms Reduction.ShakeApi.Msg.Mixed.signature_lifetime
