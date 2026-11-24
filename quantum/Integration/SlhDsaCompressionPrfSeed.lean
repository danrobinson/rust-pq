import Integration.SlhDsaCompressionPrf
import Integration.SlhDsaCompressionWotsPre
import Integration.SlhDsaBridgeMsg

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Kronecker
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]

/-- Lift a distinguisher's address queries to queries of the actual secret PRF at the
public seed selected for this run. Its compression port remains unrestricted. -/
noncomputable def addressAt (pk : S.Node)
    (A : QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool) :=
  wrap0 (Restrict.restrictImpl (V := S.Node) (fun a : SkAdrs S.vp => some (pk,a))) A

theorem address_prf_seed_average_answer (seeds : ProbComp S.Node)
    (A : S.Node → (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hA : ∀ pk, PrfAnswerCost (A pk) q) (ρ : SubState ((Input × Output) × E)) :
    let matrix := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * ∑' pk : S.Node, PQ.Interactive.prob seeds (· = pk) *
      qPrfRealPr (skPrfC S.vp (randPrims (functions S g))) (addressAt S pk (A pk (oracle g))) matrix) ≤
    (∑ g : CompressionTables, unifW _ g * ∑' pk : S.Node, PQ.Interactive.prob seeds (· = pk) *
      qPrfIdealPr (addressAt S pk (A pk (oracle g))) matrix) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  let matrix := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
  let err := ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n))
  let right := fun (g : CompressionTables) (pk : S.Node) => qPrfIdealPr (addressAt S pk (A pk (oracle g))) matrix
  let left := fun (g : CompressionTables) (pk : S.Node) => qPrfRealPr (skPrfC S.vp (randPrims (functions S g)))
    (addressAt S pk (A pk (oracle g))) matrix
  have point (pk : S.Node) : (∑ g : CompressionTables, unifW _ g * left g pk) ≤
      (∑ g : CompressionTables, unifW _ g * right g pk) + err := by
    let r := fun a : SkAdrs S.vp => some (pk,a)
    have real (g : CompressionTables) : qPrfRealPr (addressScheme S g pk) (A pk (oracle g)) matrix = left g pk :=
      QMsg.qPrfRealPr_restrict r _ _ rfl (fun _ _ => rfl) (A pk (oracle g)) matrix
    have ideal (g : CompressionTables) : qPrfIdealPr (A pk (oracle g)) matrix = right g pk := by
      apply QMsg.qPrfIdealPr_restrict r
      · intro a b v ha hb
        exact congrArg Prod.snd (Option.some.inj (ha.trans hb.symm))
      · apply QMsg.allQ_true_of
        rintro (j|n|a) <;> trivial
    have bound := address_prf_answer S pk (A pk) q (hA pk) ρ
    simp_rw [← real,← ideal]
    exact bound
  change (∑ g, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * left g pk) ≤
      (∑ g, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * right g pk) + err
  rw [average_seed S seeds left,average_seed S seeds right]
  refine (tsum_le_tsum (fun pk => mul_le_mul' le_rfl (point pk))).trans ?_
  simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right]
  exact add_le_add le_rfl ((mul_le_mul' (tsum_prob_eq_le_one seeds) le_rfl).trans (one_mul err).le)

theorem address_prf_seed_average (seeds : ProbComp S.Node)
    (A : S.Node → (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hA : ∀ pk, PU (A pk) q) (ρ : SubState ((Input × Output) × E)) :
    let matrix := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * ∑' pk : S.Node, PQ.Interactive.prob seeds (· = pk) *
      qPrfRealPr (skPrfC S.vp (randPrims (functions S g))) (addressAt S pk (A pk (oracle g))) matrix) ≤
    (∑ g : CompressionTables, unifW _ g * ∑' pk : S.Node, PQ.Interactive.prob seeds (· = pk) *
      qPrfIdealPr (addressAt S pk (A pk (oracle g))) matrix) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  exact address_prf_seed_average_answer S seeds A q (fun pk => (hA pk).toPUE.prfAnswerCost) ρ

end Reduction.Compression
#print axioms Reduction.Compression.address_prf_seed_average
