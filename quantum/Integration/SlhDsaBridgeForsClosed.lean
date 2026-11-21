import Integration.SlhDsaBridgeFors
import Integration.SlhDsaBridgeMachFors

/-!
# The FORS-leaf TCR term (`tcrFv`), closed (game side `qfors` + machine side `qtcr`)

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

`tcrFv_term` (`Integration/SlhDsaBridgeFors.lean`, agent `qfors`) consumes the hybrid-model
hypothesis `hModel`; `forsTcr_hModel` (`Integration/SlhDsaBridgeMachFors.lean`) proves it with
`q' = q + forsMHashes Link.vp qs = q + (openCounts128s qs).tcrFv`.  Result: the `hfv` hypothesis
of `composed_of_linear_eps` with `eFv = epsTcr0 (q + (openCounts128s qs).tcrFv)`, under the
forger's resource bounds and `1 ≤ c.tl` only.

The `dspr` term is NOT closed here: no `dspr` term theorem of `qfors` exists yet, and the
`dspr` model (`forsDspr_hModel`) still takes the named hypothesis `hRows`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

set_option linter.unusedSectionVars false

namespace Reduction

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **The FORS-leaf TCR term, closed**, with the count of `openCounts128s qs`. -/
theorem tcrFv_term_closed_128s (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      epsTcr0 (q + (openCounts128s qs).tcrFv) := by
  rw [← (forsMHashes_openCounts128s qs).1]
  exact tcrFv_term c optRand₀ pkSeedDist₀ F hn _
    (forsTcr_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs)

end closed

end Reduction

#print axioms Reduction.tcrFv_term_closed_128s
