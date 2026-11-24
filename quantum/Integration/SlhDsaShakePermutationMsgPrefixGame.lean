import Integration.SlhDsaShakePermutationMsgPrefixBound
import Integration.SlhDsaShakePermutationMsgHonest

namespace Reduction.ShakePermutation.MsgEffect
open Classical MLink SLHDSA Quantum PQ.Interactive OracleComp OracleSpec SetOracle MsgTrajectory ENNReal
open scoped ComplexOrder
set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.swapInjections
noncomputable section
variable (S : Sha2Set) {E Z : Type} [Fintype E] [DecidableEq E]

theorem programmed_prefix (π σ : Permutation)
    (pre : (Port → Words) → Closed (WS Port Words E) Z) (hp : PUE (spec:=unifSpec) cnt0 pre (2^41))
    (post : S.Node → Z → Closed (WS Port Words E) Bool)
    (M : Matrix (WS Port Words E) (WS Port Words E) ℂ) (hM : M.PosSemidef) (one : M.trace.re ≤ 1) :
    uniformMean (fun k => qWeight (· = true) (pre (oracle (programmed S k π σ)) >>= post k) M) ≤
      uniformMean (fun k => qWeight (· = true) (pre (oracle π) >>= post k) M) + ((2:ℝ≥0∞)^19)⁻¹ := by
  let u := (SkFormat.split S).symm.toEmbedding
  let t := u.trans σ.toEmbedding
  have large : 2^128 ≤ Fintype.card S.Node := by
    change 2^128 ≤ Fintype.card (Bytes _)
    rw [card_bytes']
    cases S <;> decide +kernel
  exact benchmark_column π u t large pre hp post M hM one

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.programmed_prefix
