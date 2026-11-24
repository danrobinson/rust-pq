import Integration.SlhDsaShakePermutationMsgSecurity

namespace Reduction.ShakePermutation.MsgCost
open Classical MLink SLHDSA SLHDSA.Security OracleSpec OracleComp PQ.Interactive Quantum ENNReal SetOracle QMsg
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "P" => fun π : Permutation => ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)
local notation "I" => fun π : Permutation => qPrfIdealPr (qbPrfMsgWL sufCheck (B π)) F.ρ₀
local notation "R" => fun π : Permutation => qPrfRealPr (msgPrf S.vp (P π)) (qbPrfMsgWL sufCheck (B π)) F.ρ₀

private theorem remove_term {a i b r c e f : ℝ≥0∞}
    (fin : i ≠ ⊤) (start : a+(i+b) ≤ (r+c)+e) (term : r ≤ i+f) :
    a+b ≤ c+(e+f) := by
  apply (ENNReal.add_le_add_iff_right fin).mp
  calc
    a+b+i = a+(i+b) := by ac_rfl
    _ ≤ _ := start
    _ ≤ ((i+f)+c)+e := add_le_add (add_le_add term le_rfl) le_rfl
    _ = _ := by ac_rfl

/-- Both secret-input SHAKE PRFs have been removed from the actual strong
signature experiment. The outstanding public hash games retain their
shared forward/inverse permutation. -/
theorem after_prfs (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    strongAdvantage S rand seeds F + uniformMean (fun π => qLinearIdealSide (B π) 0 0) ≤
      uniformMean (fun π => qLinearRealSide (B π) 0 0) + (((2:ℝ≥0∞)^42)⁻¹+((2:ℝ≥0∞)^18)⁻¹) := by
  have ideal (π : Permutation) : qLinearIdealSide (B π) 0 (I π) = I π + qLinearIdealSide (B π) 0 0 := by
    simp only [qLinearIdealSide,zero_add,add_assoc]
  have real (π : Permutation) : qLinearRealSide (B π) 0 (R π) = R π + qLinearRealSide (B π) 0 0 := by
    simp only [qLinearRealSide,zero_add,add_assoc]
  have plus (a b : Permutation → ℝ≥0∞) : uniformMean (fun π => a π+b π) = uniformMean a+uniformMean b := by
    simp only [uniformMean,mul_add,Finset.sum_add_distrib]
  have start := SkCost.after_sk S rand seeds F c msg hq hs hc
  simp_rw [ideal,real] at start
  rw [plus,plus] at start
  have term : uniformMean R ≤ uniformMean I + ((2:ℝ≥0∞)^18)⁻¹ :=
    signature_component S rand seeds F c msg hq hs hc
  have fin : uniformMean I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (ShakeXof.mean_le_const (fun π : Permutation => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one))
  exact remove_term fin start term

theorem euf_after_prfs (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    advantage S rand seeds F + uniformMean (fun π => qLinearIdealSide (B π) 0 0) ≤
      uniformMean (fun π => qLinearRealSide (B π) 0 0) + (((2:ℝ≥0∞)^42)⁻¹+((2:ℝ≥0∞)^18)⁻¹) := by
  have euf : advantage S rand seeds F ≤ strongAdvantage S rand seeds F :=
    Finset.sum_le_sum (fun π _ => mul_le_mul' le_rfl (quantum_euf_le_suf (experiment S rand seeds F π)))
  exact (add_le_add euf le_rfl).trans (after_prfs S rand seeds F c msg hq hs hc)
end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.after_prfs
#print axioms Reduction.ShakePermutation.MsgCost.euf_after_prfs
