import Integration.SlhDsaShakeXofSingleton
import PQ.Interactive.QromBridgeFors

namespace Reduction.ShakeXof
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder
variable (S : Sha2Set) {N : ℕ} (cap : FitsSingleton S (N := N))

def baseProblem (seeds : ProbComp S.Node) : SM_DT_TCR_SourceFinalValidity.Problem Empty S.Node (Bytes 32) S.Node S.Node :=
  .standalone { seedGen := seeds, eval := fun _ _ m => m } (openPreTargets S.vp)

def forsProblem (g : ShakeApi.RawTable S N) (seeds : ProbComp S.Node) :
    SM_DT_TCR_SourceFinalValidity.Problem Empty S.Node (Bytes 32) S.Node S.Node :=
  fvWithEval (baseProblem S seeds) (fun pk t m => (ShakeApi.primitives S (ShakeApi.extend g)).Thash pk t [m])

theorem forsProblem_eq (g : ShakeApi.RawTable S N) (seeds : ProbComp S.Node) :
    forsProblem S g seeds = forsTcrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend g)) seeds := rfl

attribute [local irreducible] openPreTargets

variable {W : Type} [Fintype W] (seeds : ProbComp S.Node)
  (A : QTcrFV_Adversary W (baseProblem S seeds))
  (forge : ShakeApi.RawTable S N → A.State → S.Node → Closed W (ℕ × S.Node))

def forsAdversary (g : ShakeApi.RawTable S N) : QTcrFV_Adversary W (forsProblem S g seeds) where
  State := A.State
  choose := A.choose
  forge := forge g
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

include cap in
/-- Quantum FORS target-collision game at a fixed public seed. Selection uses
the classical FORS challenge oracle. The second phase has a q-query model
over the shared XOF port. -/
theorem fors_fixed_tcr (pk : S.Node) (q : ℕ)
    (model : ∀ s : A.State, ∃ Mo : HybridModel (ShakeApi.Input N) (Bytes S.vp.params.m) (ℕ × S.Node) q,
      ∀ g : ShakeApi.RawTable S N, ∀ Ev : ℕ × S.Node → Prop, ∀ [DecidablePred Ev],
        Mo.prob g Ev = qWeight Ev (forge g s pk) A.ρ₀) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * tcrFvInner (forsAdversary S seeds A forge g) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞) := by
  let eps := (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞)
  rw [average_singleton S cap pk]
  have inner (g : ShakeApi.RawTable S N) :
      (∑ R : SingletonRow S, unifW _ R * tcrFvInner (forsAdversary S seeds A forge (replaceSingleton S cap pk g R)) pk) ≤ eps := by
    let th (R : SingletonRow S) := (forsProblem S (replaceSingleton S cap pk g R) seeds).th.eval
    have eval (R : SingletonRow S) (t : Bytes 32) (m : S.Node) : th R pk t m = R (t,m) := by
      exact replacedF S cap g pk R t m
    have hm (s : A.State) : ∃ Mo : HybridModel (Bytes 32 × S.Node) S.Node (ℕ × S.Node) q,
        ∀ R (Ev : ℕ × S.Node → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev (forge (replaceSingleton S cap pk g R) s pk) A.ρ₀ := by
      obtain ⟨M,hM⟩ := model s
      refine ⟨M.pullback (singletonEmbedding S cap pk) (fun R => (replaceSingleton S cap pk g R))
        (different_at (singletonEmbedding S cap pk) g), ?_⟩
      intro R Ev _
      rw [HybridModel.pullback_prob, hM]
    exact tcrFv_row_avg_le (forsProblem S g seeds) pk th eval A.choose
      (fun R s => forge (replaceSingleton S cap pk g R) s pk) A.ρ₀ q hm
  calc _ ≤ ∑ g : ShakeApi.RawTable S N, unifW _ g * eps :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (inner g)
       _ = eps := by rw [← Finset.sum_mul, sum_unifW, one_mul]


include cap in
theorem fors_tcr_bound (q : ℕ)
    (model : ∀ (pk : S.Node) (s : A.State), ∃ Mo : HybridModel (ShakeApi.Input N) (Bytes S.vp.params.m) (ℕ × S.Node) q,
      ∀ g : ShakeApi.RawTable S N, ∀ Ev : ℕ × S.Node → Prop, ∀ [DecidablePred Ev],
        Mo.prob g Ev = qWeight Ev (forge g s pk) A.ρ₀) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qTcrFV_Advantage (forsAdversary S seeds A forge g)) ≤
      (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  let eps := (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞)
  have num : eps = (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
    dsimp only [eps]
    rw [card_bytes', pow_mul]; norm_num
  apply le_trans _ num.le
  let f := fun g pk => tcrFvInner (forsAdversary S seeds A forge g) pk
  simp only [qTcrFV_Advantage_eq_tsum]
  change (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ eps
  calc _ = ∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : ShakeApi.RawTable S N, unifW _ g * f g pk := by
          simp only [tsum_fintype, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
       _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * eps :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fors_fixed_tcr S cap seeds A forge pk q (model pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := ENNReal.tsum_mul_right
       _ ≤ 1 * eps := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
       _ = eps := one_mul eps

include cap in
/-- Quantitative FORS bound for a port-uniform q-query quantum second phase.
The initial state may be any density matrix on the machine registers. -/
theorem fors_tcr_port {E : Type} [Fintype E] [DecidableEq E]
    (adv : QTcrFV_Adversary (Work S N E) (baseProblem S seeds))
    (machine : ShakeApi.RawTable S N → adv.State → S.Node → Closed (Work S N E) (ℕ × S.Node))
    (q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => machine H st pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qTcrFV_Advantage (forsAdversary S seeds adv machine g)) ≤
      (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  classical
  apply fors_tcr_bound S cap seeds adv machine q
  intro pk st
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (ShakeApi.Input N × Bytes S.vp.params.m) × E) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  obtain ⟨Mo,hMo⟩ := (hq st pk).exists_model ρ
  exact ⟨Mo, fun g Ev _ => (hMo g Ev).trans (by rw [hρ])⟩

end Reduction.ShakeXof

#print axioms Reduction.ShakeXof.forsProblem_eq
#print axioms Reduction.ShakeXof.fors_tcr_port
