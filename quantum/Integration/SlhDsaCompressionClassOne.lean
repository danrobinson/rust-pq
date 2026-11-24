import Integration.SlhDsaCompressionWotsTcr

namespace Reduction.Compression.ClassOne
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
open scoped ComplexOrder
variable (S : Sha2Set)

abbrev Msg := { xs : List S.Node // xs.length = 1 }
def asMsg (m : S.Node) : Msg S := ⟨[m], rfl⟩
def node (m : Msg S) : S.Node := m.val[0]'(by rw [m.property]; decide)

theorem asMsg_node (m : Msg S) : asMsg S (node S m) = m := by
  obtain ⟨l,h⟩ := m
  obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp h
  rfl

abbrev Row := Bytes 22 × Msg S → S.Node
def raw (R : Row S) : SingletonRow S := fun x => R (x.1,asMsg S x.2)
def view (r : SingletonRow S) : Row S := fun x => r (x.1,node S x.2)

theorem view_raw (R : Row S) : view S (raw S R) = R := by
  funext x
  simp only [view,raw,asMsg_node]

theorem raw_view (r : SingletonRow S) : raw S (view S r) = r := by
  funext x
  rfl

theorem avg (pk : S.Node) (f : CompressionTables → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ g, unifW _ g * ∑ R : Row S, unifW _ R * f (replaceSingleton S pk g (raw S R)) := by
  apply SetOracle.avg_resample (fun g R => replaceSingleton S pk g (raw S R))
    (fun g => view S (readSingleton S g pk))
  rintro ⟨g,R⟩
  have inv := swap_singleton S pk (g,raw S R)
  apply Prod.ext
  · change replaceSingleton S pk (replaceSingleton S pk g (raw S R)) (raw S (view S (readSingleton S g pk))) = g
    rw [raw_view]
    kexact congrArg (Prod.fst : CompressionTables × SingletonRow S → CompressionTables) inv
  · change view S (readSingleton S _ pk) = R
    rw [read_replaced, view_raw]

theorem model {D E : Type} [Fintype E] [DecidableEq E] (g : CompressionTables) (pk : S.Node)
    (A : (Input → Output) → Closed (WS Input Output E) D)
    (ρ : Matrix (WS Input Output E) (WS Input Output E) ℂ) (pos : ρ.PosSemidef) (tr : ρ.trace = 1)
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 A q) :
    ∃ M : HybridModel (Bytes 22 × Msg S) S.Node D q, ∀ R (Ev : D → Prop) [DecidablePred Ev],
      M.prob R Ev = qWeight Ev (A (oracle (replaceSingleton S pk g (raw S R)))) ρ := by
  classical
  obtain ⟨M,hM⟩ := singletonModel S g pk A ρ pos tr q hq
  let emb : (Bytes 22 × Msg S) ↪ (Bytes 22 × S.Node) :=
    ⟨fun x => (x.1,node S x.2), fun x y eq => Prod.ext (congrArg (Prod.fst : Bytes 22 × S.Node → Bytes 22) eq)
      ((asMsg_node S x.2).symm.trans ((congrArg (asMsg S) (congrArg (Prod.snd : Bytes 22 × S.Node → S.Node) eq)).trans (asMsg_node S y.2)))⟩
  refine ⟨M.pullback emb (raw S) (fun R T x h => ⟨(x.1,asMsg S x.2),rfl,h⟩), ?_⟩
  intro R Ev _
  rw [HybridModel.pullback_prob,hM]

def base (seeds : ProbComp S.Node) : SM_DT_TCR_Problem Unit S.Node (Bytes 22) (Msg S) S.Node where
  th := ⟨seeds, fun _ _ x => node S x⟩
  thColl := (basePre S seeds).thColl
  numTargets := arityTargets S.vp 1

def classHash (g : CompressionTables) (pk : S.Node) (a : Bytes 22) (x : Msg S) : S.Node :=
  (tablePrimitives g S.vp.params).Thash pk a x.1

def problem (seeds : ProbComp S.Node) (g : CompressionTables) := tcrWithEval (base S seeds)
  (classHash S g) (collection S g)

theorem problem_eq (seeds : ProbComp S.Node) (g : CompressionTables) :
    problem S seeds g = thashArityProblemT S.vp (randPrims (functions S g)) seeds 1 := rfl

attribute [local irreducible] arityTargets

variable {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
  (A : QSM_DT_TCR_Adversary (WS Input Output E) (base S seeds))
  (forge : (Input → Output) → A.State → S.Node → Closed (WS Input Output E) (ℕ × Msg S))

def adversary (g : CompressionTables) : QSM_DT_TCR_Adversary (WS Input Output E) (problem S seeds g) where
  State := A.State
  choose := A.choose
  forge := forge (oracle g)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private noncomputable def rowAdv (pk : S.Node) (g : CompressionTables) (R : Row S)
    (th : S.Node → Bytes 22 → Msg S → S.Node) (ce : Unit → S.Node → Bytes 22 → List S.Node → S.Node) :
    QSM_DT_TCR_Adversary (WS Input Output E) (tcrWithEval (base S seeds) th ce) where
  State := A.State
  choose := A.choose
  forge := forge (oracle (replaceSingleton S pk g (raw S R)))
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem abstract_row (evalLeaf : Row S → S.Node → Bytes 22 → Msg S → S.Node)
    (evalCollection : Row S → Unit → S.Node → Bytes 22 → List S.Node → S.Node) (pk : S.Node)
    (he : ∀ R a m, evalLeaf R pk a m = R (a,m))
    (hl : ∀ R T i a xs, (∀ m, R (a,m) = T (a,m)) → evalCollection R i pk a xs = evalCollection T i pk a xs) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) (g : CompressionTables) :
    (∑ R : Row S, unifW _ R * tcrInner (rowAdv S seeds A forge pk g R (evalLeaf R) (evalCollection R)) pk) ≤
      (2*(q:ℝ≥0∞)+1)^2 / (Fintype.card S.Node : ℝ≥0∞) := by
  exact tcr_row_avg_le (base S seeds) pk evalLeaf he evalCollection hl
    A.choose (fun R s => forge (oracle (replaceSingleton S pk g (raw S R))) s pk) A.ρ₀ q
    (fun s => model S g pk _ A.ρ₀ A.posSemidef A.trace_eq_one q (hq s))

private theorem row_class_tcr (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) (g : CompressionTables) :
    (∑ R : Row S, unifW _ R * tcrInner (adversary S seeds A forge (replaceSingleton S pk g (raw S R))) pk) ≤
      epsTcr S q := by
  let th := fun R => classHash S (replaceSingleton S pk g (raw S R))
  let ce := fun R => collection S (replaceSingleton S pk g (raw S R))
  have h := abstract_row S seeds A forge th ce pk (fun R a x => by
    change (tablePrimitives _ _).Thash pk a x.val = _
    rw [← show [node S x] = x.val from congrArg Subtype.val (asMsg_node S x)]
    exact (replacedF S g pk (raw S R) a (node S x)).trans (congrArg (fun m => R (a,m)) (asMsg_node S x)))
    (fun R T _ a xs he => wideCollection_local S hw g pk (raw S R) (raw S T) a xs (fun m => he (asMsg S m))) q hq g
  have card : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by rw [card_bytes',pow_mul]; norm_num
  refine h.trans ?_
  unfold epsTcr
  rw [card]

theorem wide_class_tcr_fixed (hw : S.vp.params.n ≠ 16) (pk : S.Node) (q : ℕ)
    (hq : ∀ s, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * tcrInner (adversary S seeds A forge g) pk) ≤
      epsTcr S q := by
  rw [avg S pk (fun g => tcrInner (adversary S seeds A forge g) pk)]
  calc _ ≤ ∑ g : CompressionTables, unifW _ g * epsTcr S q :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (row_class_tcr S seeds A forge hw pk q hq g)
       _ = _ := by rw [← Finset.sum_mul, sum_unifW, one_mul]

theorem wide_class_tcr_port (hw : S.vp.params.n ≠ 16) (q : ℕ)
    (hq : ∀ s pk, PUE (spec := unifSpec) cnt0 (fun H => forge H s pk) q) :
    (∑ g : CompressionTables, unifW _ g * qSM_DT_TCR_Advantage (adversary S seeds A forge g)) ≤
      epsTcr S q := by
  let f := fun g pk => tcrInner (adversary S seeds A forge g) pk
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change (∑ g : CompressionTables, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) ≤ _
  rw [average_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * epsTcr S q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (wide_class_tcr_fixed S seeds A forge hw pk q (fun s => hq s pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * epsTcr S q := ENNReal.tsum_mul_right
       _ ≤ _ := ((mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le)

end Reduction.Compression.ClassOne
#print axioms Reduction.Compression.ClassOne.wide_class_tcr_port
