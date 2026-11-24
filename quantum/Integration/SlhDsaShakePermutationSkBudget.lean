import Integration.SlhDsaShakePermutationSkBridge

namespace Reduction.ShakePermutation.SkCost
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg ENNReal ShakeApi
open Compression.SkGame (ans_bind ans_classical answer_uniform body checkedBody qbPrfWC_draw)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
open scoped Kronecker
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)

noncomputable def machine : SkGames.Machine S E := fun H =>
  qbPrfWC (vp:=S.vp) (prims:=ShakeApi.primitives S (extend (table S N H))) sufCheck
    (qPureBytesToInternal (forgerAt S rand seeds F (extend (table S N H)) H))

theorem machine_cost (cap : N ≤ rawCap S 67 65536) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PrfAnswerCost (E:=E) (D:=S.Node × SkAdrs S.vp) (R:=S.Node) (machine S N rand seeds F) (budget S q qs) := by
  intro a
  let base : Xof S := fun _ => default
  let total (d : S.Node × Adrs) : S.Node := if h : SkDom S.vp d.2 then a (d.1, ⟨d.2,h⟩) else default
  have eq (H : Port → Words) : ansRun a (machine S N rand seeds F H) =
        (liftU seeds >>= fun pk => answered S N base rand total F pk H) := by
    rw [machine,qbPrfWC_draw,Compression.drawThen,ans_bind,ans_classical,answer_uniform]
    apply bind_congr
    intro pk
    unfold checkedBody
    rw [← ansRun_restrict _ total a (fun d => by by_cases h : SkDom S.vp d.2 <;> simp [total,skRestrict,h])]
    exact (answer_body S N rand seeds F H total pk).trans (answered_eq S N rand F base H total pk)
  have h := PUE.liftU_bind (EvalCost.const (X := Port) (Y := Words) seeds)
      (fun pk => answered_cost S N base rand total F cap pk q qs hq hs)
  have h' := h.mono (Nat.le_of_eq (Nat.add_zero _))
  exact (congrArg (fun G => PUE (spec := unifSpec) cnt0 G (budget S q qs)) (funext eq)).mpr h'

/-- The native secret-address PRF hybrid at the external signing budget,
with all remaining honest hash roles using the bounded SHAKE domain. -/
theorem signature_component (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    let A := machine S (rawCap S 67 65536) rand seeds F
    SetOracle.uniformMean (fun π : Permutation => qPrfRealPr (skPrfC S.vp (primitives (lanes π) S.vp.params)) (A (oracle π)) F.ρ₀) ≤
      SetOracle.uniformMean (fun π : Permutation => qPrfIdealPr (A (oracle π)) F.ρ₀) + ((2:ℝ≥0∞)^42)⁻¹ := by
  intro A
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Port × Words) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  rw [hρ]
  exact SkGames.benchmark S A ρ (fun a => (machine_cost S _ rand seeds F le_rfl _ _ hq hs a).mono (benchmark_budget S))

end Reduction.ShakePermutation.SkCost
#print axioms Reduction.ShakePermutation.SkCost.signature_component
