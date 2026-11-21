import Integration.SlhDsaAll

/-!
# SLH-DSA-SHA2-128s against all quantum forgers (integration)

NOT part of the default target; checked by `scripts/check-integration.sh`.

The unconditional quantum headlines of `Integration/SlhDsaAll.lean` at the concrete parameter set
SLH-DSA-SHA2-128s (`Link.vp`, `Link.prims`, wire codec `codec128s`), with the structural
hypothesis discharged by `structural_128s` — no hypothesis at all: for every quantum forger with
classical signing queries (any finite workspace `W`, any initial state, arbitrary amplitudes),
every `optRand` and every `pkSeedDist`.  Sixteen theorems `slhdsa_sha2_128s_*_quantum_all`:
internal / external pure / byte-level internal / byte-level external pure; EUF-CMA and SUF-CMA;
absolute and linear form.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction

variable {W : Type} [Fintype W]
variable (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
  (pkSeedDist : ProbComp Link.prims.PkSeed)

/-- **EUF-CMA of SLH-DSA-SHA2-128s (internal algorithms, typed) against every quantum forger.** -/
theorem slhdsa_sha2_128s_euf_cma_final_quantum_all
    (Q : QForger W (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo Q :=
  slhdsa_euf_cma_final_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (internal algorithms, typed) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_euf_cma_final_linear_quantum_all
    (Q : QForger W (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf Q ≤ qLinRealEuf Q :=
  slhdsa_euf_cma_final_linear_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (internal algorithms, typed) against every quantum forger.** -/
theorem slhdsa_sha2_128s_suf_cma_final_quantum_all
    (Q : QForger W (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo Q :=
  slhdsa_suf_cma_final_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (internal algorithms, typed) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_suf_cma_final_linear_quantum_all
    (Q : QForger W (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf Q ≤ qLinRealSuf Q :=
  slhdsa_suf_cma_final_linear_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (external pure interface, typed) against every quantum forger.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final_quantum_all
    (Q : QForger W (externalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qToInternal Q) :=
  slhdsa_pure_euf_cma_final_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (external pure interface, typed) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final_linear_quantum_all
    (Q : QForger W (externalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qToInternal Q) ≤ qLinRealEuf (qToInternal Q) :=
  slhdsa_pure_euf_cma_final_linear_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (external pure interface, typed) against every quantum forger.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final_quantum_all
    (Q : QForger W (externalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qToInternal Q) :=
  slhdsa_pure_suf_cma_final_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (external pure interface, typed) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final_linear_quantum_all
    (Q : QForger W (externalAlg Link.vp Link.prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qToInternal Q) ≤ qLinRealSuf (qToInternal Q) :=
  slhdsa_pure_suf_cma_final_linear_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (internal algorithms on byte strings) against every quantum forger.** -/
theorem slhdsa_sha2_128s_bytes_euf_cma_final_quantum_all
    (Q : QForger W (bytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qBytesToTyped Q) :=
  slhdsa_bytes_euf_cma_final_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (internal algorithms on byte strings) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_bytes_euf_cma_final_linear_quantum_all
    (Q : QForger W (bytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qBytesToTyped Q) ≤ qLinRealEuf (qBytesToTyped Q) :=
  slhdsa_bytes_euf_cma_final_linear_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (internal algorithms on byte strings) against every quantum forger.** -/
theorem slhdsa_sha2_128s_bytes_suf_cma_final_quantum_all
    (Q : QForger W (bytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qBytesToTyped Q) :=
  slhdsa_bytes_suf_cma_final_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (internal algorithms on byte strings) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_bytes_suf_cma_final_linear_quantum_all
    (Q : QForger W (bytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qBytesToTyped Q) ≤ qLinRealSuf (qBytesToTyped Q) :=
  slhdsa_bytes_suf_cma_final_linear_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (external pure interface on byte strings) against every quantum forger.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_final_quantum_all
    (Q : QForger W (pureBytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemo (qPureBytesToInternal Q) :=
  slhdsa_pure_bytes_euf_cma_final_quantum_all structural_128s Q

/-- **EUF-CMA of SLH-DSA-SHA2-128s (external pure interface on byte strings) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_final_linear_quantum_all
    (Q : QForger W (pureBytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qPureBytesToInternal Q) ≤ qLinRealEuf (qPureBytesToInternal Q) :=
  slhdsa_pure_bytes_euf_cma_final_linear_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (external pure interface on byte strings) against every quantum forger.** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_final_quantum_all
    (Q : QForger W (pureBytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemo (qPureBytesToInternal Q) :=
  slhdsa_pure_bytes_suf_cma_final_quantum_all structural_128s Q

/-- **SUF-CMA of SLH-DSA-SHA2-128s (external pure interface on byte strings) against every quantum forger, linear
form.** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_final_linear_quantum_all
    (Q : QForger W (pureBytesAlg Link.vp Link.prims codec128s optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qPureBytesToInternal Q) ≤ qLinRealSuf (qPureBytesToInternal Q) :=
  slhdsa_pure_bytes_suf_cma_final_linear_quantum_all structural_128s Q

end Reduction

#print axioms Reduction.slhdsa_sha2_128s_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_suf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_suf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_bytes_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_bytes_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_bytes_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_bytes_suf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_final_linear_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_final_quantum_all
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_final_linear_quantum_all
