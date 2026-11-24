import Integration.SlhDsaShakePermutationLongBankGame
import Integration.SlhDsaShakePermutationLongBankRisk

namespace Reduction.ShakePermutation.Long.BankRun
open Classical SparsePort MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle ItsrLabel
noncomputable section
variable (S : Sha2Set) (ar : ℕ) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (A : QSM_DT_TCR_Adversary (ArityGame.Work E) (ArityGame.Base S ar seeds))
variable (forge : (Port → Words) → A.State → S.Node → Closed (ArityGame.Work E) (ℕ × Arity.Msg S ar))

theorem conditioned (pk : S.Node) (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    (h : ar ≤ 67) (q : ℕ) (hq : q ≤ 2^100)
    (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) q)
    (post : ∀ st, PUE (spec:=unifSpec) cnt0 (fun H => forge H st pk) (2^41)) (witness : TargetReady S ar pk π) :
    uniformMean (fun H : Table => tcrInner (ArityGame.adversary S ar seeds A forge (perm π H)) pk) ≤
      ((2:ℝ≥0∞)^28)⁻¹ + ((2:ℝ≥0∞)^97)⁻¹ := by
  apply (conditioned_of_step S ar seeds A forge pk π hp he h q hq count post witness (graphRate (3*2^100))
    (fun D => graph_step π hp he D (3*2^100))).trans
  exact add_le_add le_rfl (graph_budget (Nat.mul_le_mul_left 3 hq))
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.conditioned
