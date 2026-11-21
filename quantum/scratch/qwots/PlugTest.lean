import Integration.SlhDsaBridgeWotsClosed
open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
namespace Reduction
variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
example (F : PortForger (EncX c) EncY E) (q qs : ℕ) (htl : 35 ≤ c.tl)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    True := by
  have := composed_of_linear_eps (c := c) (optRand := optRandOf c optRand₀)
    (pkSeedDist := fun _ ↦ pkSeedDist₀) (internalΩ c optRand₀ pkSeedDist₀ encΩ F)
    (eUd := epsUdTight (q + (openCounts128s qs).ud)) (ePre := epsPre0 (q + (openCounts128s qs).pre))
    (hud := ud_closed c optRand₀ pkSeedDist₀ F q qs htl hq hqs)
    (hpre := pre_closed c optRand₀ pkSeedDist₀ F q qs htl hq hqs)
  trivial
end Reduction
