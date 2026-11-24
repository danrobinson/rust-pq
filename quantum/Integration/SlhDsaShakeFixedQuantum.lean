import Integration.SlhDsaAllGeneral
import MReduction.Shake

namespace ShakeSecurity
open MLink Reduction SLHDSA SLHDSA.Security PQ.Interactive OracleComp OracleSpec Quantum

/-- On the concrete SHAKE pure byte scheme the forgery probabilities reduce to
hash games on the fixed FIPS functions. Numerical estimates of those games
are the cryptographic assumptions required at a particular attack cost. -/
theorem fixed_pure_quantum_security (S : Sha2Set)
    (rand : PublicKeyCore (prims S).core → ProbComp (prims S).Y)
    (seeds : ProbComp (prims S).PkSeed) {W : Type} [Fintype W]
    (Q : QForger W (pureBytesAlg S.vp (prims S) (wireCodec S.vp.params) rand seeds)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG (qPureBytesToInternal Q) ∧
    qUnforgeableAdvantage Q ≤ qBetaEufMemoG (qPureBytesToInternal Q) :=
  ⟨slhdsa_pure_bytes_suf_cma_final_quantum_all_general (structural S) Q,
    slhdsa_pure_bytes_euf_cma_final_quantum_all_general (structural S) Q⟩

end ShakeSecurity
#print axioms ShakeSecurity.fixed_pure_quantum_security
