import Integration.SlhDsaBridgeTcrT
import Integration.SlhDsaBridgeMachWots

/-!
# The WOTS-chain TCR term (`tcrT`), closed

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

`tcrT_term` (`Integration/SlhDsaBridgeTcrT.lean`, game side) with `tcrT_hModel`
(`Integration/SlhDsaBridgeMachWots.lean`, machine side) at `q' = q + qmWotsTcrTHashes Link.vp qs
= q + (openCounts128s qs).tcrT`: the `hT` hypothesis of `composed_of_linear_eps`, under the
forger's resource bounds and `1 ≤ c.tl` only.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

set_option linter.unusedSectionVars false

namespace Reduction

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **The WOTS-chain TCR term, closed**, with the count of `openCounts128s qs`. -/
theorem tcrT_term_closed_128s (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
        epsTcr0 (q + (openCounts128s qs).tcrT) := by
  rw [← qmWotsTcrTHashes_openCounts128s qs]
  exact tcrT_term c optRand₀ pkSeedDist₀ F hn _
    (tcrT_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs)

end closed

end Reduction

#print axioms Reduction.tcrT_term_closed_128s
