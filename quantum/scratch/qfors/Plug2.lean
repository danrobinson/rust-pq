import Integration.SlhDsaBridgeForsDspr
import Integration.SlhDsaBridgeMachFors
open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
namespace Reduction
variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n)) (F : PortForger (EncX c) EncY E)
example (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hRows : ∀ (x : QuantumComp LocalSig.instruments.{0} (qromSpec (EncX c) EncY)
        (fun _ ↦ ℕ × Bool) (progReg (EncX c) EncY E)) (ρ : SubState ((EncX c × EncY) × E))
        (hx : x.IsQueryBound (fun _ ↦ q + forsMHashes Link.vp qs)),
      PQ.QROM.Rows.RowsBound (fun H Ev ↦ ((PQ.QROM.HybridModel.ofProgram
        LocalSig.Interp.instruments x ρ (q + forsMHashes Link.vp qs) hx Sigma.snd).prob H Ev).toReal)
        (q + forsMHashes Link.vp qs)) :
    avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qDsprFV_SPProbability
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) +
        epsDsprTight (q + (openCounts128s qs).dspr) := by
  rw [← (forsMHashes_openCounts128s qs).2]
  exact dspr_term c optRand₀ pkSeedDist₀ F hn _
    (forsDspr_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs hRows)
end Reduction
