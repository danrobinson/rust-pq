import Integration.SlhDsaBridgeMachWots
import Integration.SlhDsaBridgeTcrT
open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
namespace Reduction
example {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E) (hn : 1 ≤ c.tl) (q qs : ℕ)
  (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
  avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 (q + (openCounts128s qs).tcrT) := by
  rw [← qmWotsTcrTHashes_openCounts128s]
  exact tcrT_term c optRand₀ pkSeedDist₀ F hn _ (tcrT_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs)
end Reduction
