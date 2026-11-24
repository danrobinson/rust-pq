import Integration.SlhDsaCompressionPrfSeed

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Kronecker

variable {W D R α K σ : Type} [Fintype W]

/-- Sample the public seed before issuing any PRF query. -/
def drawThen (seeds : ProbComp K) (next : K → QOC W (PRFScheme.PRFOracleSpec D R) α) :=
  liftQ (liftM seeds : OracleComp (PRFScheme.PRFOracleSpec D R) K) >>= next

theorem close_draw (impl : QueryImpl (PRFScheme.PRFOracleSpec D R) (StateT σ ProbComp))
    (h : ForwardsUnif impl) (seeds : ProbComp K)
    (next : K → QOC W (PRFScheme.PRFOracleSpec D R) α) (s : σ) :
    close impl (drawThen seeds next) s = liftU seeds >>= fun k => close impl (next k) s := by
  induction seeds using OracleComp.inductionOn with
  | pure k => simp [drawThen]
  | query_bind n k ih =>
    unfold drawThen
    simp only [liftM_bind, liftQ_bind, bind_assoc,liftU_bind,liftU_query]
    rw [show (liftQ (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (PRFScheme.PRFOracleSpec D R) _) :
      QOC W (PRFScheme.PRFOracleSpec D R) _) = liftM ((instrSpec W + PRFScheme.PRFOracleSpec D R).query (.inr (.inl n))) by
        change liftQ (liftM ((PRFScheme.PRFOracleSpec D R).query (.inl n))) = _
        simp [liftQ], close_unif_bind impl h]
    exact bind_congr ih

theorem idealPr_draw [DecidableEq D] [SampleableType R] (seeds : ProbComp K)
    (next : K → QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) :
    qPrfIdealPr (drawThen seeds next) ρ = ∑' k, prob seeds (· = k) * qPrfIdealPr (next k) ρ := by
  unfold qPrfIdealPr qPrfIdealExperiment
  rw [close_draw _ forwardsUnif_prfIdeal, map_bind, qWeight_liftU_bind_tsum]

theorem realPr_draw {Key : Type} [Fintype Key] [Fintype K] (prf : PRFScheme Key D R) (seeds : ProbComp K)
    (next : K → QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) :
    qPrfRealPr prf (drawThen seeds next) ρ = ∑' k, prob seeds (· = k) * qPrfRealPr prf (next k) ρ := by
  unfold qPrfRealPr qPrfRealExperiment
  simp_rw [close_draw _ (forwardsUnif_prfReal _ _), map_bind]
  simp only [qWeight_liftU_bind_tsum,tsum_fintype,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem address_prf_sample_answer (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
    (A : S.Node → (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hq : ∀ pk, PrfAnswerCost (A pk) q) (ρ : SubState ((Input × Output) × E)) :
    let machine := fun g => drawThen seeds fun pk => addressAt S pk (A pk (oracle g))
    let matrix := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (skPrfC S.vp (randPrims (functions S g))) (machine g) matrix) ≤
      (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (machine g) matrix) +
        ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  dsimp only
  simp_rw [realPr_draw, idealPr_draw]
  exact address_prf_seed_average_answer S seeds A q hq ρ

theorem address_prf_sample (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (seeds : ProbComp S.Node)
    (A : S.Node → (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hq : ∀ pk, PU (A pk) q) (ρ : SubState ((Input × Output) × E)) :
    let machine := fun g => drawThen seeds fun pk => addressAt S pk (A pk (oracle g))
    let matrix := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (skPrfC S.vp (randPrims (functions S g))) (machine g) matrix) ≤
      (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (machine g) matrix) +
        ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  exact address_prf_sample_answer S seeds A q (fun pk => (hq pk).toPUE.prfAnswerCost) ρ

end Reduction.Compression
#print axioms Reduction.Compression.address_prf_sample
