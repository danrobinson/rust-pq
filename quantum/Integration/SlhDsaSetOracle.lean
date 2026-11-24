import Integration.SlhDsaComposedClosed
import Integration.SlhDsaAllGeneral
import MReduction.Instances

namespace Reduction.SetOracle

open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive Quantum ENNReal

abbrev codecFor (S : Sha2Set) (f : RandFns S.vp.params) :
    CoreWireCodec S.vp.params (randPrims f).core :=
  let c := MReduction.codec S
  ⟨c.pkSeed, c.skSeed, c.skPrf, c.y, c.y_toBytes⟩

abbrev Input (S : Sha2Set) (c : Caps) :=
  (S.Node × Bytes 22 × BList S.Node c.tl) ⊕
  ((S.Node × S.Node × S.Node × BList Byte c.ml) ⊕
  ((S.Node × S.Node × Bytes 22) ⊕ (S.Node × S.Node × BList Byte c.ml)))

abbrev Output (S : Sha2Set) := S.Node × Bytes S.vp.params.m

noncomputable instance (S : Sha2Set) (c : Caps) : DecidableEq (Input S c) := Classical.decEq _

def oracle (S : Sha2Set) {c : Caps} (g : FinFns S.vp.params c) : Input S c → Output S
  | .inl x => (g.thash x.1 x.2.1 x.2.2, 0)
  | .inr (.inl x) => (0, g.hmsg x.1 x.2.1 x.2.2.1 x.2.2.2)
  | .inr (.inr (.inl x)) => (g.prf x.1 x.2.1 x.2.2, 0)
  | .inr (.inr (.inr x)) => (g.prfMsg x.1 x.2.1 x.2.2, 0)

variable (S : Sha2Set) (c : Caps) (rand : S.Node → S.Node → ProbComp S.Node)
  (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
  (F : PortForger (Input S c) (Output S) E)

noncomputable abbrev scheme (g : FinFns S.vp.params c) :=
  pureBytesAlg S.vp (randPrims g.toRand) (codecFor S g.toRand)
    (fun pk => rand pk.pkSeed pk.pkRoot) seeds

noncomputable abbrev forgerAt (g : FinFns S.vp.params c) :=
  F.at (oracle S g) (scheme S c rand seeds g)

/-- All-set starting point for the quantitative component bounds. -/
theorem suf_linear :
    (∑ g, unifW (FinFns S.vp.params c) g * qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g)) +
    (∑ g, unifW (FinFns S.vp.params c) g *
      qLinIdealSufG (qPureBytesToInternal (forgerAt S c rand seeds F g))) ≤
    ∑ g, unifW (FinFns S.vp.params c) g *
      qLinRealSufG (qPureBytesToInternal (forgerAt S c rand seeds F g)) :=
  avg_of_pointwise _ _ _ _ fun g =>
    slhdsa_pure_bytes_suf_cma_final_linear_quantum_all_general
      (structural_randPrims S.vp (fipsApprovedAddressBounds S.fips) g.toRand) _

/-- The generic port experiment recovers the closed 128s result, with the original
query and encoded-message restrictions. -/
theorem suf_128s (rand : Sha2Set.s128s.Node → Sha2Set.s128s.Node → ProbComp Sha2Set.s128s.Node)
    (seeds : ProbComp Sha2Set.s128s.Node) (F : PortForger (Input .s128s c) (Output .s128s) E)
    (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (ht : 35 ≤ c.tl) :
    (∑ g, unifW (FinFns Sha2Set.s128s.vp.params c) g *
      qStrongUnforgeableAdvantage (forgerAt .s128s c rand seeds F g)) ≤
        composedBoundFinal q qs (openCounts128s qs).noPrfMsg := by
  have port (g : Ω128 c) : oracle .s128s g = encΩ g := by
    funext x
    rcases x with x | x | x | x <;> rfl
  have alg (g : Ω128 c) : scheme .s128s c rand seeds g = algΩ c rand seeds g := rfl
  apply le_trans (b := avΩ c (fun g => qStrongUnforgeableAdvantage
    (F.at (encΩ g) (algΩ c rand seeds g))))
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro g _
    unfold forgerAt
    rw [port g, alg g]
    rfl
  exact slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed c rand seeds F q qs hq hqs hc ht

end Reduction.SetOracle

#print axioms Reduction.SetOracle.suf_linear
#print axioms Reduction.SetOracle.suf_128s
