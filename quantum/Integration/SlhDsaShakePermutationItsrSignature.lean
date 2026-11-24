import Integration.SlhDsaShakePermutationRemaining
import Integration.SlhDsaShakePermutationItsrSearch
import Integration.SlhDsaShakePermutationItsrCandidates

namespace Reduction.ShakePermutation
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal SetOracle
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536

theorem signature_itsr (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    messageTerm S rand seeds F ≤ ((2:ℝ≥0∞)^81)⁻¹ := by
  have cap : Completion.blockCap N ≤ 483 := by cases S <;> decide +kernel
  have raw : 3*S.vp.params.n+c.ml ≤ N := by rw [msg]; cases S <;> decide +kernel
  have b := ItsrLabel.search_benchmark S cap (ItsrCost.candidates S N rand seeds F)
    (ItsrCost.candidates_cost S N rand seeds F le_rfl hq hs) F.ρ₀ F.posSemidef F.trace_eq_one
  exact (Classic.mean_mono (ItsrCost.pair_reduction S N rand seeds F c raw hs hc)).trans b

theorem two_remaining (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let total := ((2:ℝ≥0∞)^81)⁻¹ + arityTerm S rand seeds F S.vp.params.len +
      arityTerm S rand seeds F S.vp.params.k + ((2:ℝ≥0∞)^17)⁻¹
    strongAdvantage S rand seeds F ≤ total ∧ advantage S rand seeds F ≤ total := by
  have h := three_remaining S rand seeds F c msg hq hs hc
  have m := signature_itsr S rand seeds F c msg hq hs hc
  exact ⟨h.1.trans (add_le_add (add_le_add (add_le_add m le_rfl) le_rfl) le_rfl),
    h.2.trans (add_le_add (add_le_add (add_le_add m le_rfl) le_rfl) le_rfl)⟩

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.signature_itsr
#print axioms Reduction.ShakePermutation.two_remaining
