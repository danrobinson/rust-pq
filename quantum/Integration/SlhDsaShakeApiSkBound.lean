import Integration.SlhDsaShakeApiSkBridge

namespace Reduction.ShakeApi.Sk
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg
open Compression.SkGame (answerImpl ans_bind ans_classical answer_uniform ans_wrap body checkedBody qbPrfWC_draw)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
open scoped Kronecker
variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)

/-- The complete secret-address reduction, including sampling its public seed, has one
joint budget for the adversary's coherent calls and the honest classical evaluations. -/
theorem machine_cost (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PrfAnswerCost (E := E) (D := S.Node × SkAdrs S.vp) (R := S.Node)
      (fun H : RawTable S N => qbPrfWC (vp := S.vp) (prims := primitives S (extend H)) sufCheck
        (qPureBytesToInternal (rawForger S N rand seeds F H)))
      (budget S q qs) := by
  intro a
  let base : Xof S := fun _ => default
  let total (d : S.Node × Adrs) : S.Node := if h : SkDom S.vp d.2 then a (d.1, ⟨d.2,h⟩) else default
  have eq (H : RawTable S N) :
      ansRun a (qbPrfWC sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))) =
        (liftU seeds >>= fun pk => answered S N base rand total F pk H) := by
    rw [qbPrfWC_draw,Compression.drawThen,ans_bind,ans_classical,answer_uniform]
    apply bind_congr
    intro pk
    unfold checkedBody
    rw [← ansRun_restrict _ total a (fun d => by by_cases h : SkDom S.vp d.2 <;> simp [total,skRestrict,h])]
    exact (answer_body S N rand seeds F H total pk).trans (answered_eq S N rand F base H total pk)
  have h := PUE.liftU_bind (EvalCost.const (X := Input N) (Y := Bytes S.vp.params.m) seeds)
      (fun pk => answered_cost S N base rand total F pk q qs hq hs)
  have h' := h.mono (Nat.le_of_eq (Nat.add_zero _))
  apply (congrArg (fun G => PUE (spec := unifSpec) cnt0 G (budget S q qs)) (funext eq)).mpr
  exact h'

theorem real_le_ideal (cap : 2*S.vp.params.n+32 ≤ N)
    (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    let A := fun H : RawTable S N => qbPrfWC sufCheck (qPureBytesToInternal (rawForger S N rand seeds F H))
    SetOracle.uniformMean (fun H => qPrfRealPr (skPrfC S.vp (primitives S (extend H))) (A H) F.ρ₀) ≤
      SetOracle.uniformMean (fun H => qPrfIdealPr (A H) F.ρ₀) +
        ENNReal.ofReal (8*(budget S q qs : ℝ)^2 / 2^(8*S.vp.params.n)) := by
  intro A
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input N × Bytes S.vp.params.m) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  rw [hρ]
  exact ShakeXof.sk_prf S cap A _ (machine_cost S N rand seeds F q qs hq hs) ρ

end Reduction.ShakeApi.Sk
#print axioms Reduction.ShakeApi.Sk.real_le_ideal
