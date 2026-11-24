import Integration.SlhDsaCompressionRow
import PQ.Interactive.QromBridgeFors

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder
variable (S : Sha2Set)

def baseProblem (seeds : ProbComp S.Node) : SM_DT_TCR_SourceFinalValidity.Problem Empty S.Node (Bytes 22) S.Node S.Node :=
  .standalone { seedGen := seeds, eval := fun _ _ m => m } (openPreTargets S.vp)

def forsProblem (g : CompressionTables) (seeds : ProbComp S.Node) :
    SM_DT_TCR_SourceFinalValidity.Problem Empty S.Node (Bytes 22) S.Node S.Node :=
  fvWithEval (baseProblem S seeds) (fun pk t m => (tablePrimitives g S.vp.params).Thash pk t [m])

theorem forsProblem_eq (g : CompressionTables) (seeds : ProbComp S.Node) :
    forsProblem S g seeds = forsTcrProblem S.vp (tablePrimitives g S.vp.params) seeds := rfl

attribute [local irreducible] openPreTargets

variable {W : Type} [Fintype W] (seeds : ProbComp S.Node)
  (A : QTcrFV_Adversary W (baseProblem S seeds))
  (forge : (Input → Output) → A.State → S.Node → Closed W (ℕ × S.Node))

def forsAdversary (g : CompressionTables) : QTcrFV_Adversary W (forsProblem S g seeds) where
  State := A.State
  choose := A.choose
  forge := forge (oracle g)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

/-- Quantum FORS target-collision game at a fixed public seed. Selection uses
the classical FORS challenge oracle. The second phase has a q-query model
over the shared compression port. -/
theorem fors_fixed_tcr (pk : S.Node) (q : ℕ)
    (model : ∀ s : A.State, ∃ Mo : HybridModel Input Output (ℕ × S.Node) q,
      ∀ g : CompressionTables, ∀ Ev : ℕ × S.Node → Prop, ∀ [DecidablePred Ev],
        Mo.prob (oracle g) Ev = qWeight Ev (forge (oracle g) s pk) A.ρ₀) :
    (∑ g : CompressionTables, unifW _ g * tcrFvInner (forsAdversary S seeds A forge g) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞) := by
  let eps := (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞)
  rw [average_singleton S pk]
  have inner (g : CompressionTables) :
      (∑ R : SingletonRow S, unifW _ R * tcrFvInner (forsAdversary S seeds A forge (replaceSingleton S pk g R)) pk) ≤ eps := by
    let th (R : SingletonRow S) := (forsProblem S (replaceSingleton S pk g R) seeds).th.eval
    have eval (R : SingletonRow S) (t : Bytes 22) (m : S.Node) : th R pk t m = R (t,m) := by
      exact (singleton_eval S (replaceSingleton S pk g R) pk t m).trans
        (congrFun (read_replaced S pk g R) (t,m))
    have hm (s : A.State) : ∃ Mo : HybridModel (Bytes 22 × S.Node) S.Node (ℕ × S.Node) q,
        ∀ R (Ev : ℕ × S.Node → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev (forge (oracle (replaceSingleton S pk g R)) s pk) A.ρ₀ := by
      obtain ⟨M,hM⟩ := model s
      refine ⟨M.pullback (singletonEmbedding S g pk) (fun R => oracle (replaceSingleton S pk g R))
        (singleton_local S g pk), ?_⟩
      intro R Ev _
      rw [HybridModel.pullback_prob, hM]
    exact tcrFv_row_avg_le (forsProblem S g seeds) pk th eval A.choose
      (fun R s => forge (oracle (replaceSingleton S pk g R)) s pk) A.ρ₀ q hm
  calc _ ≤ ∑ g : CompressionTables, unifW _ g * eps :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (inner g)
       _ = eps := by rw [← Finset.sum_mul, sum_unifW, one_mul]


theorem fors_tcr_bound (q : ℕ)
    (model : ∀ (pk : S.Node) (s : A.State), ∃ Mo : HybridModel Input Output (ℕ × S.Node) q,
      ∀ g : CompressionTables, ∀ Ev : ℕ × S.Node → Prop, ∀ [DecidablePred Ev],
        Mo.prob (oracle g) Ev = qWeight Ev (forge (oracle g) s pk) A.ρ₀) :
    (∑ g : CompressionTables, unifW _ g * qTcrFV_Advantage (forsAdversary S seeds A forge g)) ≤
      (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  let eps := (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞)
  have num : eps = (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
    dsimp only [eps]
    rw [card_bytes', pow_mul]; norm_num
  apply le_trans _ num.le
  let f := fun g pk => tcrFvInner (forsAdversary S seeds A forge g) pk
  simp only [qTcrFV_Advantage_eq_tsum]
  change (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ eps
  calc _ = ∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : CompressionTables, unifW _ g * f g pk := by
          simp only [tsum_fintype, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
       _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * eps :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fors_fixed_tcr S seeds A forge pk q (model pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := ENNReal.tsum_mul_right
       _ ≤ 1 * eps := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
       _ = eps := one_mul eps

/-- Quantitative FORS bound for a port-uniform q-query quantum second phase.
The initial state may be any density matrix on the machine registers. -/
theorem fors_tcr_port {E : Type} [Fintype E] [DecidableEq E]
    (adv : QTcrFV_Adversary (WS Input Output E) (baseProblem S seeds))
    (machine : (Input → Output) → adv.State → S.Node → Closed (WS Input Output E) (ℕ × S.Node))
    (q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => machine H st pk) q) :
    (∑ g : CompressionTables, unifW _ g * qTcrFV_Advantage (forsAdversary S seeds adv machine g)) ≤
      (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  classical
  apply fors_tcr_bound S seeds adv machine q
  intro pk st
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  obtain ⟨Mo,hMo⟩ := (hq st pk).exists_model ρ
  exact ⟨Mo, fun g Ev _ => (hMo (oracle g) Ev).trans (by rw [hρ])⟩

end Reduction.Compression

#print axioms Reduction.Compression.forsProblem_eq
#print axioms Reduction.Compression.fors_tcr_port
