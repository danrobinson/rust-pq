import Integration.SlhDsaShakeXofTweak

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder

theorem mean_seed {X P : Type} [Fintype X] [Fintype P] (seeds : ProbComp P) (f : X → P → ℝ≥0∞) :
    SetOracle.uniformMean (fun x => ∑' pk, PQ.Interactive.prob seeds (· = pk) * f x pk) =
    ∑' pk, PQ.Interactive.prob seeds (· = pk) * SetOracle.uniformMean (fun x => f x pk) := by
  simp only [SetOracle.uniformMean,tsum_fintype,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mean_le_const {X : Type} [Fintype X] [Nonempty X] {f : X → ℝ≥0∞} {b : ℝ≥0∞} (h : ∀ x, f x ≤ b) :
    SetOracle.uniformMean f ≤ b := by
  calc _ ≤ ∑ x : X, unifW _ x * b := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (h x)
       _ = _ := by rw [← Finset.sum_mul,sum_unifW,one_mul]

namespace Arity
variable (S : Sha2Set) (ar : ℕ)
abbrev Msg := SetOracle.ArMsg S ar
abbrev Row := Bytes 32 × Msg S ar → S.Node
variable {N : ℕ} (seeds : ProbComp S.Node)
def base : SM_DT_TCR_Problem Unit S.Node (Bytes 32) (Msg S ar) S.Node where
  th := ⟨seeds,fun _ _ _ => default⟩
  thColl := ⟨fun _ => List S.Node,fun _ _ _ _ => default⟩
  numTargets := arityTargets S.vp ar

def problem (g : ShakeApi.RawTable S N) : SM_DT_TCR_Problem Unit S.Node (Bytes 32) (Msg S ar) S.Node := thashArityProblemT S.vp (ShakeApi.primitives S (ShakeApi.extend g)) seeds ar

attribute [local irreducible] arityTargets tcrTargets
variable {E : Type} [Fintype E] [DecidableEq E]
  (A : QSM_DT_TCR_Adversary (Work S N E) (base S ar seeds))
  (forge : ShakeApi.RawTable S N → A.State → S.Node → Closed (Work S N E) (ℕ × Msg S ar))

def adversary (g : ShakeApi.RawTable S N) : QSM_DT_TCR_Adversary (Work S N E) (problem S ar seeds g) where
  State := A.State
  choose := A.choose
  forge := forge g
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

theorem fixed (pk : S.Node) (cap : S.vp.params.n + 32 + S.vp.params.n*ar ≤ N)
    (q : ℕ) (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    SetOracle.uniformMean (fun g => tcrInner (adversary S ar seeds A forge g) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  let : Nonempty (Msg S ar) := ⟨⟨List.replicate ar default, by simp⟩⟩
  let nodes : Msg S ar → List S.Node := Subtype.val
  have hi : Function.Injective nodes := Subtype.val_injective
  have hc (m : Msg S ar) : S.vp.params.n + 32 + S.vp.params.n * (nodes m).length ≤ N := by
    change _ + _ * m.val.length ≤ N
    rw [m.property]; exact cap
  let emb := thEmb S pk nodes hi hc
  refine (resample emb (node_le_digest S) (fun g => tcrInner (adversary S ar seeds A forge g) pk)).le.trans ?_
  apply mean_le_const
  intro g
  let put := write emb g (n := S.vp.params.n)
  let th := fun (R : Row S ar) (p : S.Node) (a : Bytes 32) (x : Msg S ar) =>
    (ShakeApi.primitives S (ShakeApi.extend (put R))).Thash p a x.val
  let ce := fun (R : Row S ar) (_ : Unit) (p : S.Node) (a : Bytes 32) (xs : List S.Node) =>
    (ShakeApi.primitives S (ShakeApi.extend (put R))).Thash p a xs
  have bound := tcr_row_avg_le (base S ar seeds) pk th (thLeaf S pk nodes hi hc g)
    ce (fun R T _ a xs => thLocal S pk nodes hi hc g R T a xs) A.choose
    (fun R s => forge (put R) s pk) A.ρ₀ q
    (fun s => slice_model emb g _ A.ρ₀ A.posSemidef A.trace_eq_one q (hq s))
  have card : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by rw [card_bytes',pow_mul]; norm_num
  rw [← card]
  exact bound

/-- Arity-class TCR, for every phase-one transcript over the collection and
every bounded second-phase algorithm with quantum access to the shared XOF. -/
theorem bound (cap : S.vp.params.n + 32 + S.vp.params.n*ar ≤ N) (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    SetOracle.uniformMean (fun g => qSM_DT_TCR_Advantage (adversary S ar seeds A forge g)) ≤
      (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  let eps : ℝ≥0∞ := (2*(q:ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n)
  let f (g : ShakeApi.RawTable S N) (pk : S.Node) := tcrInner (adversary S ar seeds A forge g) pk
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change SetOracle.uniformMean (fun g => ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ eps
  rw [mean_seed seeds f]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * eps :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fixed S ar seeds A forge pk cap q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := ENNReal.tsum_mul_right
       _ ≤ _ := ((mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le)

end Arity
end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.Arity.bound
