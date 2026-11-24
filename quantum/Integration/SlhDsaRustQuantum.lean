import Integration.SlhDsaAllGeneral
import ME2E.Api.Sha2_128s
import ME2E.Api.Sha2_128f
import ME2E.Api.Sha2_192s
import ME2E.Api.Sha2_192f
import ME2E.Api.Sha2_256s
import ME2E.Api.Sha2_256f

/-!
# Quantum chosen-message security of the pure SHA-2 Rust API

The first conjunct identifies the Rust byte operations with the classical signer,
key generator and verifier in the experiment. The other conjuncts reduce quantum
forgery against the concrete SHA-2 functions to quantum hash games.
-/

namespace ME2E

open MLink MReduction Reduction SLHDSA SLHDSA.Security PQ.Interactive
open OracleComp OracleSpec Quantum

/-- Select the implementation correspondence for the actual per-set API. -/
def RustApiCorrespondence : (S : Sha2Set) →
    (PublicKeyCore S.prims.core → ProbComp S.prims.Y) → ProbComp S.prims.PkSeed → Prop
  | .s128s => sha2_128s.ApiPureBytesEndToEnd
  | .s128f => sha2_128f.ApiPureBytesEndToEnd
  | .s192s => sha2_192s.ApiPureBytesEndToEnd
  | .s192f => sha2_192f.ApiPureBytesEndToEnd
  | .s256s => sha2_256s.ApiPureBytesEndToEnd
  | .s256f => sha2_256f.ApiPureBytesEndToEnd

theorem api_pure_quantum_security (S : Sha2Set)
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (W : Type) [Fintype W] :
    RustApiCorrespondence S optRand pkSeedDist ∧
    ∀ Q : QForger W (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist),
      qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG (qPureBytesToInternal Q) ∧
      qUnforgeableAdvantage Q ≤ qBetaEufMemoG (qPureBytesToInternal Q) := by
  constructor
  · cases S
    · exact sha2_128s.api_pure_bytes_end_to_end optRand pkSeedDist
    · exact sha2_128f.api_pure_bytes_end_to_end optRand pkSeedDist
    · exact sha2_192s.api_pure_bytes_end_to_end optRand pkSeedDist
    · exact sha2_192f.api_pure_bytes_end_to_end optRand pkSeedDist
    · exact sha2_256s.api_pure_bytes_end_to_end optRand pkSeedDist
    · exact sha2_256f.api_pure_bytes_end_to_end optRand pkSeedDist
  · intro Q
    exact ⟨slhdsa_pure_bytes_suf_cma_final_quantum_all_general (structural S) Q,
      slhdsa_pure_bytes_euf_cma_final_quantum_all_general (structural S) Q⟩

end ME2E

#print axioms ME2E.api_pure_quantum_security
