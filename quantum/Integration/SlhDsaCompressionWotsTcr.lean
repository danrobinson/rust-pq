import Integration.SlhDsaCompressionWotsPre

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
variable (S : Sha2Set)
def baseWotsTcr (seeds : ProbComp S.Node) : SM_DT_TCR_Problem Unit S.Node (Bytes 22) S.Node S.Node where
  th := (basePre S seeds).th
  thColl := (basePre S seeds).thColl
  numTargets := wotsStepTargetsT S.vp

noncomputable def epsTcr (S : Sha2Set) (q : ℕ) : ℝ≥0∞ := (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n)

def chainTcrProblem (seeds : ProbComp S.Node) (g : CompressionTables) := tcrWithEval (baseWotsTcr S seeds)
  (leafHash S g) (collection S g)

theorem chainTcrProblem_eq (seeds : ProbComp S.Node) (g : CompressionTables) :
    chainTcrProblem S seeds g = wotsTcrProblemT S.vp (randPrims (functions S g)) seeds := rfl

attribute [local irreducible] wotsStepTargetsT

variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_TCR_Adversary (WS Input Output E) (baseWotsTcr S seeds))
  (forge : (Input → Output) → A.State → S.Node → Closed (WS Input Output E) (ℕ × S.Node))

def chainTcrAdversary (g : CompressionTables) : QSM_DT_TCR_Adversary (WS Input Output E) (chainTcrProblem S seeds g) where
  State := A.State
  choose := A.choose
  forge := forge (oracle g)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private noncomputable def rowAdv (pk : S.Node) (g : CompressionTables) (R : SingletonRow S)
    (th : S.Node → Bytes 22 → S.Node → S.Node) (ce : Unit → S.Node → Bytes 22 → List S.Node → S.Node) :
    QSM_DT_TCR_Adversary (WS Input Output E) (tcrWithEval (baseWotsTcr S seeds) th ce) where
  State := A.State
  choose := A.choose
  forge := forge (oracle (replaceSingleton S pk g R))
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem abstract_row (evalLeaf : SingletonRow S → S.Node → Bytes 22 → S.Node → S.Node)
    (evalCollection : SingletonRow S → Unit → S.Node → Bytes 22 → List S.Node → S.Node) (pk : S.Node)
    (he : ∀ R a m, evalLeaf R pk a m = R (a,m))
    (hl : ∀ R T i a xs, (∀ m, R (a,m) = T (a,m)) → evalCollection R i pk a xs = evalCollection T i pk a xs) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) (g : CompressionTables) :
    (∑ R : SingletonRow S, unifW _ R * tcrInner (rowAdv S seeds A forge pk g R (evalLeaf R) (evalCollection R)) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞) := by
  exact tcr_row_avg_le (baseWotsTcr S seeds) pk evalLeaf he evalCollection hl
    A.choose (fun R s => forge (oracle (replaceSingleton S pk g R)) s pk) A.ρ₀ q
    (fun s => singletonModel S g pk _ A.ρ₀ A.posSemidef A.trace_eq_one q (hq s))

private theorem row_chain_tcr (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) (g : CompressionTables) :
    (∑ R : SingletonRow S, unifW _ R * tcrInner (chainTcrAdversary S seeds A forge (replaceSingleton S pk g R)) pk) ≤
      epsTcr S q := by
  let th := fun R => leafHash S (replaceSingleton S pk g R)
  let ce := fun R => collection S (replaceSingleton S pk g R)
  have h := abstract_row S seeds A forge th ce pk (replacedF S g pk)
    (fun R T _ a xs => wideCollection_local S hw g pk R T a xs) q hq g
  have card : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by rw [card_bytes',pow_mul]; norm_num
  refine h.trans ?_
  unfold epsTcr
  rw [card]

theorem wide_chain_tcr_fixed (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * tcrInner (chainTcrAdversary S seeds A forge g) pk) ≤
      epsTcr S q := by
  rw [average_singleton S pk (fun g => tcrInner (chainTcrAdversary S seeds A forge g) pk)]
  calc _ ≤ ∑ g : CompressionTables, unifW _ g * epsTcr S q :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (row_chain_tcr S seeds A forge hw pk q hq g)
       _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

theorem wide_chain_tcr_port (hw : S.vp.params.n ≠ 16) (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_TCR_Advantage (chainTcrAdversary S seeds A forge g)) ≤
      epsTcr S q := by
  let f := fun g pk => tcrInner (chainTcrAdversary S seeds A forge g) pk
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ _
  rw [average_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * epsTcr S q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wide_chain_tcr_fixed S seeds A forge hw pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * epsTcr S q := ENNReal.tsum_mul_right
       _ ≤ _ := ((mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le)

end Reduction.Compression
#print axioms Reduction.Compression.wide_chain_tcr_fixed
#print axioms Reduction.Compression.wide_chain_tcr_port
