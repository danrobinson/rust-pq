import Integration.SlhDsaCompressionSmallItsrBound
import Integration.SlhDsaCompressionSmallItsrProfiles

namespace Reduction.Compression.SmallItsr
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal Classical

private theorem density {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
    (key : St → K) (bits : ℕ) (card : Fintype.card K = 2^bits)
    (uniform : ∀ P : K → Prop, Pr{let y ← $ᵗ St}[P (key y)] = Pr{let z ← $ᵗ K}[P z]) (B : Finset K) :
    ((Finset.univ.filter fun y => key y ∈ B).card : ℝ)/Fintype.card St = (B.card:ℝ)/2^bits := by
  have h := uniform (fun z => z ∈ B)
  simp only [SampleableType.prEvent_uniformSample] at h
  have e := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter,card,
    Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using e

def bits (S : Sha2Set) := if S = Sha2Set.s128f then 61 else 75

/-- The complete mixed shared-table ITSR bound for each n=16 signature
parameter set. The fast set retains all 55 upper tree bits and six FORS bits
available in MGF1 counter zero. The small set retains all 75 coordinate bits. -/
theorem small_itsr (S : Sha2Set) (hn : S.vp.params.n = 16)
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (F : PortForger Input Output E) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀)
      ≤ loss S c.ml q qs (bits S) := by
  cases S <;> try contradiction
  · let i : Fin Slow.vp.params.k := ⟨0,by decide⟩
    exact itsr_bound (Slow.key i) .s128s rfl i (Slow.covers i) 75
      (fun B => (density _ _ (by rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]; decide)
        (Slow.uniform i) B).le) r seeds F c q qs hq hs hc
  · let i : Fast.Ix := ⟨0,by decide⟩
    exact itsr_bound (Fast.key i) .s128f rfl i (Fast.covers i) 61
      (fun B => (density _ _ (by rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]; decide)
        (Fast.uniform i) B).le) r seeds F c q qs hq hs hc
end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.small_itsr
