import Integration.SlhDsaSetOracle
import Integration.SlhDsaBridgePrf
import MReduction.Instances
import MIdeal.MixedTables

/-! A single quantum port for both public compression tables. The honest scheme
uses the same tables for its SHA-2 calls, including HMAC and MGF1. -/
namespace Reduction.Compression

open SLHDSA SLHDSA.Security MLink Ideal OracleComp OracleSpec PQ.Interactive Quantum ENNReal

abbrev Input := (St × Blk) ⊕ (Chain512 × Block512)
abbrev Output := St × (Fin 8 → UInt64)

def oracle (tables : CompressionTables) : Input → Output
  | .inl x => (tables.1 x, 0)
  | .inr x => (0, arrayVectorEquivFin UInt64 8 (tables.2 x))

/-- Fixed tables determine the four SLH-DSA hash functions jointly. -/
def functions (S : Sha2Set) (tables : CompressionTables) : RandFns S.vp.params :=
  let prims := tablePrimitives tables S.vp.params
  ⟨prims.Thash, prims.Hmsg, prims.PRF, prims.PRFmsg⟩

theorem primitives_eq (S : Sha2Set) (tables : CompressionTables) :
    randPrims (functions S tables) = tablePrimitives tables S.vp.params := rfl

theorem real_primitives (S : Sha2Set) :
    randPrims (functions S (realCF, realTable512)) = S.prims :=
  (primitives_eq ..).trans (tablePrimitives_real _)

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable abbrev experimentForger (tables : CompressionTables) :=
  let f := functions S tables
  F.at (oracle tables) (pureBytesAlg S.vp (randPrims f) (SetOracle.codecFor S f)
    (fun pk => rand pk.pkSeed pk.pkRoot) seeds)

/-- Uniform independent compression tables, shared across all components and
accessible in superposition. The right-hand side still consists of hash-game
advantages evaluated with access to these same tables. -/
theorem suf_ideal_compression_reduction :
    (∑ g : CompressionTables, (Fintype.card CompressionTables : ℝ≥0∞)⁻¹ *
      qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
    ∑ g : CompressionTables, (Fintype.card CompressionTables : ℝ≥0∞)⁻¹ *
      qBetaSufMemoG (qPureBytesToInternal (experimentForger S rand seeds F g)) := by
  apply Finset.sum_le_sum
  intro g _
  exact mul_le_mul' le_rfl (slhdsa_pure_bytes_suf_cma_final_quantum_all_general
    (structural_randPrims S.vp (fipsApprovedAddressBounds S.fips) (functions S g)) _)

/-- Average the real and ideal success probabilities separately. This form permits
a game hop to compare mixtures before taking their difference. -/
theorem suf_ideal_compression_linear :
    (∑ g : CompressionTables, (Fintype.card CompressionTables : ℝ≥0∞)⁻¹ *
      qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) +
    (∑ g : CompressionTables, (Fintype.card CompressionTables : ℝ≥0∞)⁻¹ *
      qLinIdealSufG (qPureBytesToInternal (experimentForger S rand seeds F g))) ≤
    ∑ g : CompressionTables, (Fintype.card CompressionTables : ℝ≥0∞)⁻¹ *
      qLinRealSufG (qPureBytesToInternal (experimentForger S rand seeds F g)) :=
  avg_of_pointwise _ _ _ _ fun g =>
    slhdsa_pure_bytes_suf_cma_final_linear_quantum_all_general
      (structural_randPrims S.vp (fipsApprovedAddressBounds S.fips) (functions S g)) _

/-- On checked addresses the PRF and the singleton tweakable hash read the same
compression input, even when both compression tables are ideal. -/
theorem shared_singleton (tables : CompressionTables) (pk sk : S.Node) (a : Adrs)
    {chk : Concrete.Sha2Address} (ha : Concrete.Sha2Address.ofAdrs a = .ok chk) :
    (functions S tables).prf pk sk a =
      (functions S tables).thash pk (Concrete.sha2AdrsKey a) [sk] := by
  have h := Ideal.PRF_eq_Thash (liftC tables.1) S.vp.params pk sk a ha
  simpa only [functions, tablePrimitives, sha2PrimitivesMixed, sha2PrimitivesG,
    sha2ThashMixed, sha2ThashG, List.length_cons, List.length_nil, ite_true] using h

end Reduction.Compression

#print axioms Reduction.Compression.real_primitives
#print axioms Reduction.Compression.suf_ideal_compression_reduction

#print axioms Reduction.Compression.suf_ideal_compression_linear
#print axioms Reduction.Compression.shared_singleton
