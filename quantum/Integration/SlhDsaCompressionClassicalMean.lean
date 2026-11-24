import Integration.SlhDsaCompressionClassicalProgram

namespace Reduction.Compression.ClassicalPort
open Ideal MLink Quantum PQ.Interactive OracleComp ENNReal Classical MeasureTheory
private theorem scalar_mean {U V : Type} [Fintype U] [Fintype V] [DecidableEq (U × V)]
    [Fintype (CF U V)] [SampleableType (CF U V)] (f : CF U V → ℝ≥0∞) :
    cfAvg f = ∑ x, unifW _ x * f x := by
  letI : MeasurableSpace (CF U V) := ⊤
  unfold cfAvg
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [SampleableType.evalDist_uniformSample_singleton]
  exact mul_comm _ _

theorem average_eq (f : CompressionTables → ℝ≥0∞) :
    MIdeal.PureCompression.average f = SetOracle.uniformMean f := by
  unfold MIdeal.PureCompression.average SetOracle.uniformMean
  simp only [scalar_mean]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [unifW,Fintype.card_prod,Nat.cast_mul,Finset.mul_sum,ENNReal.mul_inv
    (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl
end Reduction.Compression.ClassicalPort
#print axioms Reduction.Compression.ClassicalPort.average_eq
