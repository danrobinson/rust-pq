import Integration.SlhDsaCompressionRow
import Integration.SlhDsaSetWots

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder Kronecker
variable (S : Sha2Set)

theorem replacedF (g : CompressionTables) (pk : S.Node) (R : SingletonRow S) (t : Bytes 22) (m : S.Node) :
    (tablePrimitives (replaceSingleton S pk g R) S.vp.params).Thash pk t [m] = R (t,m) :=
  (singleton_eval S _ _ _ _).trans (congrFun (read_replaced S pk g R) (t,m))

theorem wideCollection_local (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (pk : S.Node)
    (R T : SingletonRow S) (a : Bytes 22) (xs : List S.Node) (ha : ∀ m, R (a,m) = T (a,m)) :
    (tablePrimitives (replaceSingleton S pk g R) S.vp.params).Thash pk a xs =
    (tablePrimitives (replaceSingleton S pk g T) S.vp.params).Thash pk a xs := by
  by_cases h : xs.length = 1
  · obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp h
    exact (replacedF S g pk R a x).trans ((ha x).trans (replacedF S g pk T a x).symm)
  · change sha2ThashMixed _ _ _ _ _ _ = sha2ThashMixed _ _ _ _ _ _
    simp only [sha2ThashMixed, ite_eq_right h, ite_eq_right hw]
    rfl

theorem singletonModel {D E : Type} [Fintype E] [DecidableEq E]
    (g : CompressionTables) (pk : S.Node) (A : (Input → Output) → Closed (WS Input Output E) D)
    (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ) (pos : ρ.PosSemidef) (tr : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel (Bytes 22 × S.Node) S.Node D q, ∀ R (Ev : D → Prop) [DecidablePred Ev],
      M.prob R Ev = qWeight Ev (A (oracle (replaceSingleton S pk g R))) ρ := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ pos tr
  obtain ⟨M,hM⟩ := hq.exists_model σ
  refine ⟨M.pullback (singletonEmbedding S g pk) (fun R => oracle (replaceSingleton S pk g R))
    (singleton_local S g pk), ?_⟩
  intro R Ev _
  rw [HybridModel.pullback_prob, hM, hσ]

def basePre (seeds : ProbComp S.Node) : SM_DT_PRE_Problem Unit S.Node (Bytes 22) S.Node S.Node S.Node where
  th := ⟨seeds,fun _ _ m => m⟩
  emb := id
  emb_injective := Function.injective_id
  thColl := ⟨fun _ => List S.Node,fun _ p _ _ => p⟩
  numTargets := wotsChainTargets S.vp

def leafHash (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (m : S.Node) : S.Node :=
  (tablePrimitives g S.vp.params).Thash pk a [m]

def collection (g : CompressionTables) (_ : Unit) (pk : S.Node) (a : Bytes 22) (xs : List S.Node) : S.Node :=
  (tablePrimitives g S.vp.params).Thash pk a xs

def preProblem (seeds : ProbComp S.Node) (g : CompressionTables) := preWithEval (basePre S seeds)
  (leafHash S g) (collection S g)

theorem preProblem_eq (seeds : ProbComp S.Node) (g : CompressionTables) :
    preProblem S seeds g = wotsPreProblem S.vp (randPrims (functions S g)) seeds := rfl

attribute [local irreducible] wotsChainTargets

variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_PRE_Adversary (WS Input Output E) (basePre S seeds))
  (invert : (Input → Output) → A.State → S.Node → Closed (WS Input Output E) (ℕ × S.Node))

def preAdversary (g : CompressionTables) : QSM_DT_PRE_Adversary (WS Input Output E) (preProblem S seeds g) where
  State := A.State
  choose := A.choose
  invert := invert (oracle g)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private noncomputable def rowAdv (pk : S.Node) (g : CompressionTables) (R : SingletonRow S)
    (th : S.Node → Bytes 22 → S.Node → S.Node) (ce : Unit → S.Node → Bytes 22 → List S.Node → S.Node) :
    QSM_DT_PRE_Adversary (WS Input Output E) (preWithEval (basePre S seeds) th ce) where
  State := A.State
  choose := A.choose
  invert := invert (oracle (replaceSingleton S pk g R))
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem abstract_row (evalLeaf : SingletonRow S → S.Node → Bytes 22 → S.Node → S.Node)
    (evalCollection : SingletonRow S → Unit → S.Node → Bytes 22 → List S.Node → S.Node) (pk : S.Node)
    (he : ∀ R a m, evalLeaf R pk a m = R (a,m))
    (hl : ∀ R T i a xs, (∀ m, R (a,m) = T (a,m)) → evalCollection R i pk a xs = evalCollection T i pk a xs) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) (g : CompressionTables) :
    (∑ R : SingletonRow S, unifW _ R * preInner (rowAdv S seeds A invert pk g R (evalLeaf R) (evalCollection R)) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 * ((Fintype.card S.Node : ℝ≥0∞)⁻¹ + (Fintype.card S.Node : ℝ≥0∞)⁻¹) := by
  exact pre_row_avg_le (basePre S seeds) pk evalLeaf he evalCollection hl
    A.choose (fun R s => invert (oracle (replaceSingleton S pk g R)) s pk) A.ρ₀ q
    (fun s => singletonModel S g pk _ A.ρ₀ A.posSemidef A.trace_eq_one q (hq s))

private theorem row_pre (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) (g : CompressionTables) :
    (∑ R : SingletonRow S, unifW _ R * preInner (preAdversary S seeds A invert (replaceSingleton S pk g R)) pk) ≤
      SetOracle.epsPreSet S q := by
  let th := fun R => leafHash S (replaceSingleton S pk g R)
  let ce := fun R => collection S (replaceSingleton S pk g R)
  have h := abstract_row S seeds A invert th ce pk (replacedF S g pk)
    (fun R T _ a xs => wideCollection_local S hw g pk R T a xs) q hq g
  have card : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by rw [card_bytes',pow_mul]; norm_num
  refine h.trans ?_
  unfold SetOracle.epsPreSet
  rw [card]

theorem wide_pre_fixed (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * preInner (preAdversary S seeds A invert g) pk) ≤
      SetOracle.epsPreSet S q := by
  rw [average_singleton S pk (fun g => preInner (preAdversary S seeds A invert g) pk)]
  calc _ ≤ ∑ g : CompressionTables, unifW _ g * SetOracle.epsPreSet S q :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (row_pre S seeds A invert hw pk q hq g)
       _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

theorem average_seed (f : CompressionTables → S.Node → ℝ≥0∞) :
    (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) =
      ∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : CompressionTables, unifW _ g * f g pk := by
  simp only [tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wide_pre_port (hw : S.vp.params.n ≠ 16) (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => invert H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_PRE_Advantage (preAdversary S seeds A invert g)) ≤
      SetOracle.epsPreSet S q := by
  let f := fun g pk => preInner (preAdversary S seeds A invert g) pk
  simp only [qSM_DT_PRE_Advantage_eq_tsum]
  change (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ _
  rw [average_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * SetOracle.epsPreSet S q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wide_pre_fixed S seeds A invert hw pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * SetOracle.epsPreSet S q := ENNReal.tsum_mul_right
       _ ≤ _ := ((mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le)

end Reduction.Compression
#print axioms Reduction.Compression.wide_pre_fixed
#print axioms Reduction.Compression.wide_pre_port
