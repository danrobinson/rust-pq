import Integration.SlhDsaShakeXofWotsPre

namespace Reduction.ShakeXof
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
variable (S : Sha2Set) {N : ℕ} (cap : FitsSingleton S (N := N))
def baseWotsTcr (seeds : ProbComp S.Node) : SM_DT_TCR_Problem Unit S.Node (Bytes 32) S.Node S.Node where
  th := (basePre S seeds).th
  thColl := (basePre S seeds).thColl
  numTargets := wotsStepTargetsT S.vp

noncomputable def epsTcr (S : Sha2Set) (q : ℕ) : ℝ≥0∞ := (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n)

def chainTcrProblem (seeds : ProbComp S.Node) (g : ShakeApi.RawTable S N) := tcrWithEval (baseWotsTcr S seeds)
  (leafHash S g) (collection S g)

theorem chainTcrProblem_eq (seeds : ProbComp S.Node) (g : ShakeApi.RawTable S N) :
    chainTcrProblem S seeds g = wotsTcrProblemT S.vp (ShakeApi.primitives S (ShakeApi.extend g)) seeds := rfl

attribute [local irreducible] wotsStepTargetsT

variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_TCR_Adversary (Work S N E) (baseWotsTcr S seeds))
  (forge : ShakeApi.RawTable S N → A.State → S.Node → Closed (Work S N E) (ℕ × S.Node))

def chainTcrAdversary (g : ShakeApi.RawTable S N) : QSM_DT_TCR_Adversary (Work S N E) (chainTcrProblem S seeds g) where
  State := A.State
  choose := A.choose
  forge := forge g
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private noncomputable def rowAdv (pk : S.Node) (g : ShakeApi.RawTable S N) (R : SingletonRow S)
    (th : S.Node → Bytes 32 → S.Node → S.Node) (ce : Unit → S.Node → Bytes 32 → List S.Node → S.Node) :
    QSM_DT_TCR_Adversary (Work S N E) (tcrWithEval (baseWotsTcr S seeds) th ce) where
  State := A.State
  choose := A.choose
  forge := forge (replaceSingleton S cap pk g R)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem abstract_row (evalLeaf : SingletonRow S → S.Node → Bytes 32 → S.Node → S.Node)
    (evalCollection : SingletonRow S → Unit → S.Node → Bytes 32 → List S.Node → S.Node) (pk : S.Node)
    (he : ∀ R a m, evalLeaf R pk a m = R (a,m))
    (hl : ∀ R T i a xs, (∀ m, R (a,m) = T (a,m)) → evalCollection R i pk a xs = evalCollection T i pk a xs) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) (g : ShakeApi.RawTable S N) :
    (∑ R : SingletonRow S, unifW _ R * tcrInner (rowAdv S cap seeds A forge pk g R (evalLeaf R) (evalCollection R)) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞) := by
  exact tcr_row_avg_le (baseWotsTcr S seeds) pk evalLeaf he evalCollection hl
    A.choose (fun R s => forge (replaceSingleton S cap pk g R) s pk) A.ρ₀ q
    (fun s => slice_model (singletonEmbedding S cap pk) g _ A.ρ₀ A.posSemidef A.trace_eq_one q (hq s))

private theorem row_chain_tcr (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) (g : ShakeApi.RawTable S N) :
    (∑ R : SingletonRow S, unifW _ R * tcrInner (chainTcrAdversary S seeds A forge (replaceSingleton S cap pk g R)) pk) ≤
      epsTcr S q := by
  let th := fun R => leafHash S (replaceSingleton S cap pk g R)
  let ce := fun R => collection S (replaceSingleton S cap pk g R)
  have h := abstract_row S cap seeds A forge th ce pk (replacedF S cap g pk)
    (fun R T _ a xs => collection_local S cap g pk R T a xs) q hq g
  have card : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by rw [card_bytes',pow_mul]; norm_num
  refine h.trans ?_
  unfold epsTcr
  rw [card]

include cap in
theorem wots_chain_tcr_fixed (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * tcrInner (chainTcrAdversary S seeds A forge g) pk) ≤
      epsTcr S q := by
  rw [average_singleton S cap pk (fun g => tcrInner (chainTcrAdversary S seeds A forge g) pk)]
  calc _ ≤ ∑ g : ShakeApi.RawTable S N, unifW _ g * epsTcr S q :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (row_chain_tcr S cap seeds A forge pk q hq g)
       _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

include cap in
theorem wots_chain_tcr_port (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qSM_DT_TCR_Advantage (chainTcrAdversary S seeds A forge g)) ≤
      epsTcr S q := by
  let f := fun g pk => tcrInner (chainTcrAdversary S seeds A forge g) pk
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ _
  rw [average_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * epsTcr S q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wots_chain_tcr_fixed S cap seeds A forge pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * epsTcr S q := ENNReal.tsum_mul_right
       _ ≤ _ := ((mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le)

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.wots_chain_tcr_fixed
#print axioms Reduction.ShakeXof.wots_chain_tcr_port
