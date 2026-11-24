import Integration.SlhDsaShakeXofSingleton
import Integration.SlhDsaSetWots

namespace Reduction.ShakeXof
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder Kronecker
variable (S : Sha2Set) {N : ℕ} (cap : FitsSingleton S (N := N))

def basePre (seeds : ProbComp S.Node) : SM_DT_PRE_Problem Unit S.Node (Bytes 32) S.Node S.Node S.Node where
  th := ⟨seeds,fun _ _ m => m⟩
  emb := id
  emb_injective := Function.injective_id
  thColl := ⟨fun _ => List S.Node,fun _ p _ _ => p⟩
  numTargets := wotsChainTargets S.vp

def leafHash (g : ShakeApi.RawTable S N) (pk : S.Node) (a : Bytes 32) (m : S.Node) : S.Node :=
  (ShakeApi.primitives S (ShakeApi.extend g)).Thash pk a [m]

def collection (g : ShakeApi.RawTable S N) (_ : Unit) (pk : S.Node) (a : Bytes 32) (xs : List S.Node) : S.Node :=
  (ShakeApi.primitives S (ShakeApi.extend g)).Thash pk a xs

def preProblem (seeds : ProbComp S.Node) (g : ShakeApi.RawTable S N) := preWithEval (basePre S seeds)
  (leafHash S g) (collection S g)

theorem preProblem_eq (seeds : ProbComp S.Node) (g : ShakeApi.RawTable S N) :
    preProblem S seeds g = wotsPreProblem S.vp (ShakeApi.primitives S (ShakeApi.extend g)) seeds := rfl

attribute [local irreducible] wotsChainTargets

variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_PRE_Adversary (Work S N E) (basePre S seeds))
  (invert : ShakeApi.RawTable S N → A.State → S.Node → Closed (Work S N E) (ℕ × S.Node))

def preAdversary (g : ShakeApi.RawTable S N) : QSM_DT_PRE_Adversary (Work S N E) (preProblem S seeds g) where
  State := A.State
  choose := A.choose
  invert := invert g
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private noncomputable def rowAdv (pk : S.Node) (g : ShakeApi.RawTable S N) (R : SingletonRow S)
    (th : S.Node → Bytes 32 → S.Node → S.Node) (ce : Unit → S.Node → Bytes 32 → List S.Node → S.Node) :
    QSM_DT_PRE_Adversary (Work S N E) (preWithEval (basePre S seeds) th ce) where
  State := A.State
  choose := A.choose
  invert := invert (replaceSingleton S cap pk g R)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem abstract_row (evalLeaf : SingletonRow S → S.Node → Bytes 32 → S.Node → S.Node)
    (evalCollection : SingletonRow S → Unit → S.Node → Bytes 32 → List S.Node → S.Node) (pk : S.Node)
    (he : ∀ R a m, evalLeaf R pk a m = R (a,m))
    (hl : ∀ R T i a xs, (∀ m, R (a,m) = T (a,m)) → evalCollection R i pk a xs = evalCollection T i pk a xs) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) (g : ShakeApi.RawTable S N) :
    (∑ R : SingletonRow S, unifW _ R * preInner (rowAdv S cap seeds A invert pk g R (evalLeaf R) (evalCollection R)) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 * ((Fintype.card S.Node : ℝ≥0∞)⁻¹ + (Fintype.card S.Node : ℝ≥0∞)⁻¹) := by
  exact pre_row_avg_le (basePre S seeds) pk evalLeaf he evalCollection hl
    A.choose (fun R s => invert (replaceSingleton S cap pk g R) s pk) A.ρ₀ q
    (fun s => slice_model (singletonEmbedding S cap pk) g _ A.ρ₀ A.posSemidef A.trace_eq_one q (hq s))

include cap in
private theorem row_pre (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) (g : ShakeApi.RawTable S N) :
    (∑ R : SingletonRow S, unifW _ R * preInner (preAdversary S seeds A invert (replaceSingleton S cap pk g R)) pk) ≤
      SetOracle.epsPreSet S q := by
  let th := fun R => leafHash S (replaceSingleton S cap pk g R)
  let ce := fun R => collection S (replaceSingleton S cap pk g R)
  have h := abstract_row S cap seeds A invert th ce pk (replacedF S cap g pk)
    (fun R T _ a xs => collection_local S cap g pk R T a xs) q hq g
  have card : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by rw [card_bytes',pow_mul]; norm_num
  refine h.trans ?_
  unfold SetOracle.epsPreSet
  rw [card]

include cap in
theorem wots_pre_fixed (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * preInner (preAdversary S seeds A invert g) pk) ≤
      SetOracle.epsPreSet S q := by
  rw [average_singleton S cap pk (fun g => preInner (preAdversary S seeds A invert g) pk)]
  calc _ ≤ ∑ g : ShakeApi.RawTable S N, unifW _ g * SetOracle.epsPreSet S q :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (row_pre S cap seeds A invert pk q hq g)
       _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

include cap in
theorem wots_pre_port (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qSM_DT_PRE_Advantage (preAdversary S seeds A invert g)) ≤
      SetOracle.epsPreSet S q := by
  let f := fun g pk => preInner (preAdversary S seeds A invert g) pk
  simp only [qSM_DT_PRE_Advantage_eq_tsum]
  change (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ _
  rw [average_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * SetOracle.epsPreSet S q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wots_pre_fixed S cap seeds A invert pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * SetOracle.epsPreSet S q := ENNReal.tsum_mul_right
       _ ≤ _ := ((mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le)

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.wots_pre_fixed
#print axioms Reduction.ShakeXof.wots_pre_port
