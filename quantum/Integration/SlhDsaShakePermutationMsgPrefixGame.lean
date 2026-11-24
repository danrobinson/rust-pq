import Integration.SlhDsaShakePermutationMsgPrefixBound
import Integration.SlhDsaShakePermutationMsgHonest

namespace Reduction.ShakePermutation.MsgEffect
open Classical MLink SLHDSA Quantum PQ.Interactive OracleComp OracleSpec SetOracle MsgTrajectory ENNReal
open scoped ComplexOrder
set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.swapInjections
noncomputable section
variable (S : Sha2Set) {E Z : Type} [Fintype E] [DecidableEq E]

def prefixBits (S : Sha2Set) : ℕ := 4*S.vp.params.n-45

theorem programmed_prefix (π σ : Permutation)
    (pre : (Port → Words) → Closed (WS Port Words E) Z) (hp : PUE (spec:=unifSpec) cnt0 pre (2^41))
    (post : S.Node → Z → Closed (WS Port Words E) Bool)
    (M : Matrix (WS Port Words E) (WS Port Words E) ℂ) (hM : M.PosSemidef) (one : M.trace.re ≤ 1) :
    uniformMean (fun k => qWeight (· = true) (pre (oracle (programmed S k π σ)) >>= post k) M) ≤
      uniformMean (fun k => qWeight (· = true) (pre (oracle π) >>= post k) M) + ((2:ℝ≥0∞)^(prefixBits S))⁻¹ := by
  let u := (SkFormat.split S).symm.toEmbedding
  let t := u.trans σ.toEmbedding
  have large : 2^(2*(4*S.vp.params.n)) ≤ Fintype.card S.Node := by
    change _ ≤ Fintype.card (Bytes _)
    rw [card_bytes']; cases S <;> decide +kernel
  apply (column_bound (4*S.vp.params.n) π u t (by cases S <;> decide +kernel) large pre hp post M hM one).trans
  apply add_le_add le_rfl
  have size : S.vp.params.n = 16 ∨ S.vp.params.n = 24 ∨ S.vp.params.n = 32 := by cases S <;> decide
  rw [← ENNReal.ofReal_ofNat (n := 2),← ENNReal.ofReal_pow (by norm_num),← ENNReal.ofReal_inv_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rcases size with h|h|h <;> norm_num [prefixBits,h,fee,cost]

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.programmed_prefix
