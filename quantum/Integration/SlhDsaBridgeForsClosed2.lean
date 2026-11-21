import Integration.SlhDsaBridgeForsDspr
import Integration.SlhDsaBridgeMachFors2

/-!
# The FORS-leaf DSPR term (`dspr`), closed (game side `qfors` + machine side `qtcr`)

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

`dspr_term` (`Integration/SlhDsaBridgeForsDspr.lean`, agent `qfors`) consumes the additive,
rows-bounded model hypothesis; `forsDspr_hModel'` (`Integration/SlhDsaBridgeMachFors2.lean`)
proves it with `q' = q + forsMHashes Link.vp qs = q + (openCounts128s qs).dspr`.  Result: the
`hdspr` hypothesis of `composed_of_linear_eps` with `eDspr = epsDsprTight (q + (openCounts128s
qs).dspr)`, under the forger's resource bounds and `1 ≤ c.tl` only.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

set_option linter.unusedSectionVars false

namespace Reduction

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **The FORS-leaf DSPR term, closed**, with the count of `openCounts128s qs`. -/
theorem dspr_term_closed_128s (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qDsprFV_SPProbability
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) +
        epsDsprTight (q + (openCounts128s qs).dspr) := by
  rw [← (forsMHashes_openCounts128s qs).2]
  exact dspr_term c optRand₀ pkSeedDist₀ F hn _
    (forsDspr_hModel' c optRand₀ pkSeedDist₀ F q qs hq hqs)

end closed

end Reduction

#print axioms Reduction.dspr_term_closed_128s
