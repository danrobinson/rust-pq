import Integration.SlhDsaShakeSignatureItsr
import Integration.SlhDsaShakeXofBenchmark
import Integration.SlhDsaSetEuf

namespace Reduction.ShakeXof
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
variable (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
  (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend H)
local notation "A" => ShakeApi.rawForger S N r seeds F
local notation "B" => fun H => qPureBytesToInternal (A H)
local notation "Q" => (2^41 : ℕ)
local notation "n" => (8*S.vp.params.n)
local notation "prf" => ENNReal.ofReal (8*(Q:ℝ)^2 / 2^n)
local notation "tcr" => ((2*(Q:ℝ≥0∞)+1)^2 / 2^n)

set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives ShakeApi.primitives ShakeApi.scheme
attribute [local irreducible] arityTargets tcrTargets

/-- Composition for the actual SHAKE byte-level port. Each component hypothesis
concerns the very same sampled XOF; distinguishing games are averaged before
taking the difference. -/
theorem compose_benchmark (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (sk : uniformMean (fun H => qPrfRealPr (skPrfC S.vp (P H)) (qbPrfWC sufCheck (B H)) F.ρ₀) ≤
      uniformMean (fun H => qPrfIdealPr (qbPrfWC sufCheck (B H)) F.ρ₀) + prf)
    (msg : uniformMean (fun H => qPrfRealPr (msgPrf S.vp (P H)) (qbPrfMsgWL sufCheck (B H)) F.ρ₀) ≤
      uniformMean (fun H => qPrfIdealPr (qbPrfMsgWL sufCheck (B H)) F.ρ₀) + prf)
    (dspr : uniformMean (fun H => qDsprFV_Success (qToDspr (B H))) ≤
      uniformMean (fun H => qDsprFV_SPProbability (qToDspr (B H))) + ENNReal.ofReal (168*(Q:ℝ)^2 / 2^n))
    (fv : uniformMean (fun H => qTcrFV_Advantage (qToTcr (B H))) ≤ tcr)
    (ar : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], uniformMean (fun H => qSM_DT_TCR_Advantage (qbTcrArM k (B H))) ≤ tcr)
    (ud : uniformMean (fun H => qSM_DT_UD_RealSuccess (qrUd (B H))) ≤
      uniformMean (fun H => qSM_DT_UD_IdealSuccess (qrUd (B H))) + SetOracle.epsUdSet S Q)
    (pre : uniformMean (fun H => qSM_DT_PRE_Advantage (qrPre (B H))) ≤ SetOracle.epsPreSet S Q)
    (chain : uniformMean (fun H => qSM_DT_TCR_Advantage (qrTcrT (B H))) ≤ tcr) :
    uniformMean (fun H => qStrongUnforgeableAdvantage (A H)) ≤ ((2:ℝ≥0∞)^36)⁻¹ ∧
    uniformMean (fun H => qUnforgeableAdvantage (A H)) ≤ ((2:ℝ≥0∞)^36)⁻¹ := by
  have hl := avg_of_pointwise (unifW (ShakeApi.RawTable S N)) _ _ _ (fun H => slhdsa_pure_bytes_suf_cma_final_linear_quantum_all
    (ShakeApi.structural S (ShakeApi.extend H)) (A H))
  simp only [qLinRealSuf,qLinIdealSuf] at hl
  have h := ShakeSingle.signature_itsr S N r seeds F c raw (2^40) hq hs hc
  have hn : (2^40:ℕ) + itsrHashes S.vp 1 ≤ Q := by cases S <;> decide +kernel
  have hi := h.trans (ENNReal.ofReal_le_ofReal (show (16:ℝ)*(_+1)^3/_ ≤ 16*((Q:ℝ)+1)^3/2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) by gcongr))
  have all := SetOracle.composeFamily S.vp P B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one)
    (fun _ => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one) hl sk msg hi dspr fv
    (ar 1 (by simp)) (ar 2 (by simp)) (ar _ (by simp)) (ar _ (by simp)) ud pre chain
  have suf := all.trans (singleLoss_benchmark S)
  exact ⟨suf,(Finset.sum_le_sum fun H _ => mul_le_mul' (a:=unifW _ H) le_rfl (quantum_euf_le_suf (A H))).trans suf⟩

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.compose_benchmark
