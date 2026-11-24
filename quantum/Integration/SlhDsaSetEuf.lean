import Integration.SlhDsaSetClosed
import Integration.QuantumForgeryFreshness

namespace Reduction.SetOracle
open MLink PQ.Interactive ENNReal
theorem euf_closed (S : Sha2Set) (c : Caps) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (F : PortForger (Input S c) (Output S) E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ht : max 2 (max S.vp.params.len S.vp.params.k) ≤ c.tl) :
    avg S c (fun g => qUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤
      componentForgeryBound S q qs :=
  (avg_mono S c fun _ => quantum_euf_le_suf _).trans (suf_closed S c rand seeds F q qs hq hs hc ht)
end Reduction.SetOracle

#print axioms Reduction.SetOracle.euf_closed
