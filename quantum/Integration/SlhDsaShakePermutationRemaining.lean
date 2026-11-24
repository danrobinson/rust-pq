import Integration.SlhDsaShakePermutationMsgSecondHybrid
import Integration.SlhDsaShakePermutationForsSignature
import Integration.SlhDsaShakePermutationDsprSignature
import Integration.SlhDsaShakePermutationSparseSignature
import Integration.SlhDsaShakePermutationWotsUdSignature
import Integration.SlhDsaShakePermutationWotsPreSignature
import Integration.SlhDsaShakePermutationWotsChainSignature

/-! Native two-way quantum signature reduction after all short-input hash games.
The remaining terms use the same sampled permutation as the signature game. -/
namespace Reduction.ShakePermutation
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal SetOracle
open SparsePort
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "P" => fun π : Permutation => ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)

noncomputable def messageTerm := uniformMean (fun π => qItsrAdvantage (itsrProblem S.vp (P π)) (qbItsrL (B π)) F.ρ₀)
noncomputable def arityTerm (ar : ℕ) := uniformMean (fun π => qSM_DT_TCR_Advantage (qbTcrArM ar (B π)))

theorem three_remaining_width (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let remaining := messageTerm S rand seeds F + arityTerm S rand seeds F S.vp.params.len + arityTerm S rand seeds F S.vp.params.k
    strongAdvantage S rand seeds F ≤ remaining + (((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ + ((2:ℝ≥0∞)^29)⁻¹) ∧
    advantage S rand seeds F ≤ remaining + (((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ + ((2:ℝ≥0∞)^29)⁻¹) := by
  dsimp only
  let e : ℕ → ℝ≥0∞ := fun k => ((2:ℝ≥0∞)^k)⁻¹
  let d := e 42 + MsgCost.messageFee S
  let win := fun π => qStrongUnforgeableAdvantage (experiment S rand seeds F π)
  have start := MsgCost.after_prfs_width S rand seeds F c msg hq hs hc
  have eq (π : Permutation) : qLinearRealSide (B π) d 0 = qLinearRealSide (B π) 0 0 + d := by
    have move (p t u v w x y : ℝ≥0∞) : p+t+u+v+w+x+y = t+u+v+w+x+y+p := by ac_rfl
    simp only [qLinearRealSide,add_zero,zero_add]
    exact move ..
  have lin : uniformMean win + uniformMean (fun π => qLinearIdealSide (B π) 0 0) ≤ uniformMean (fun π => qLinearRealSide (B π) d 0) := by
    simp_rw [eq]
    have plus (f g : Permutation → ℝ≥0∞) : uniformMean (fun π => f π + g π) = uniformMean f + uniformMean g := by simp only [uniformMean,mul_add,Finset.sum_add_distrib]
    rw [plus,SparsePort.const_mean]
    kexact start
  have both := composeFamily S.vp P B win (fun _ => d) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    d 0 (messageTerm S rand seeds F) (e 31) (e 38) (e 38) (e 38)
    (arityTerm S rand seeds F S.vp.params.len) (arityTerm S rand seeds F S.vp.params.k) (e 35) (e 37) (e 38)
    (fun _ => zero_le) (fun _ => zero_le) lin
    (by rw [SparsePort.const_mean,SparsePort.const_mean,zero_add]) (by simp only [add_zero,le_refl]) le_rfl
    (ForsDecision.signature_dspr S rand seeds F hq hs) (Fors.signature_tcr S rand seeds F hq hs)
    (Memo.signature_tcr S 1 rand seeds F (by decide) hq hs) (Memo.signature_tcr S 2 rand seeds F (by decide) hq hs)
    le_rfl le_rfl (Wots.Ud.signature_ud S rand seeds F hq hs) (Wots.Pre.signature_pre S rand seeds F hq hs)
    (Wots.Chain.signature_chain S rand seeds F hq hs)
  let x := messageTerm S rand seeds F
  let y := arityTerm S rand seeds F S.vp.params.len
  let z := arityTerm S rand seeds F S.vp.params.k
  have w : S.vp.params.w-2 = 14 := by cases S <;> decide
  rw [w] at both
  have budget : d+0+(e 31+3*e 38)+(e 38+e 38)+(14:ℕ)*e 35+e 37+e 38 ≤ e (MsgEffect.prefixBits S) + e 29 := by
    dsimp only [d,e,MsgCost.messageFee]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
      ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_zero]
    linarith [show ((2:ℝ)^42)⁻¹+((2:ℝ)^40)⁻¹+(((2:ℝ)^31)⁻¹+3*((2:ℝ)^38)⁻¹)+2*((2:ℝ)^38)⁻¹+14*((2:ℝ)^35)⁻¹+((2:ℝ)^37)⁻¹+((2:ℝ)^38)⁻¹ ≤ ((2:ℝ)^29)⁻¹ by norm_num]
  have arrange (d x y z a f u p t : ℝ≥0∞) :
      d+0+x+(a+3*f)+(f+f+y+z)+(14:ℕ)*u+p+t = x+y+z+(d+0+(a+3*f)+(f+f)+(14:ℕ)*u+p+t) := by ac_rfl
  have strong : strongAdvantage S rand seeds F ≤ x+y+z+(e (MsgEffect.prefixBits S) + e 29) := both.trans (le_trans (le_of_eq (arrange d x y z (e 31) (e 38) (e 35) (e 37) (e 38))) (add_le_add le_rfl budget))
  exact ⟨strong,(Finset.sum_le_sum fun π _ => mul_le_mul' le_rfl (quantum_euf_le_suf (experiment S rand seeds F π))).trans strong⟩

theorem three_remaining_precise (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let remaining := messageTerm S rand seeds F + arityTerm S rand seeds F S.vp.params.len + arityTerm S rand seeds F S.vp.params.k
    strongAdvantage S rand seeds F ≤ remaining + (((2:ℝ≥0∞)^18)⁻¹ + ((2:ℝ≥0∞)^29)⁻¹) ∧
    advantage S rand seeds F ≤ remaining + (((2:ℝ≥0∞)^18)⁻¹ + ((2:ℝ≥0∞)^29)⁻¹) := by
  have both := three_remaining_width S rand seeds F c msg hq hs hc
  have fee : ((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ ≤ ((2:ℝ≥0∞)^18)⁻¹ := by
    exact (le_self_add ..).trans (MsgCost.messageFee_le S)
  exact ⟨both.1.trans (add_le_add le_rfl (add_le_add fee le_rfl)),both.2.trans (add_le_add le_rfl (add_le_add fee le_rfl))⟩

theorem three_remaining (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let remaining := messageTerm S rand seeds F + arityTerm S rand seeds F S.vp.params.len + arityTerm S rand seeds F S.vp.params.k
    strongAdvantage S rand seeds F ≤ remaining + ((2:ℝ≥0∞)^17)⁻¹ ∧
    advantage S rand seeds F ≤ remaining + ((2:ℝ≥0∞)^17)⁻¹ := by
  have h := three_remaining_precise S rand seeds F c msg hq hs hc
  have budget : ((2:ℝ≥0∞)^18)⁻¹ + ((2:ℝ≥0∞)^29)⁻¹ ≤ ((2:ℝ≥0∞)^17)⁻¹ := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    norm_num
  exact ⟨h.1.trans (add_le_add le_rfl budget), h.2.trans (add_le_add le_rfl budget)⟩

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.three_remaining_precise
#print axioms Reduction.ShakePermutation.three_remaining
