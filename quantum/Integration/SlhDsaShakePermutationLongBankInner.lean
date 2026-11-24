import Integration.SlhDsaShakePermutationLongBankConditioned
import Integration.SlhDsaShakePermutationLongBankTarget

namespace Reduction.ShakePermutation.Long.BankRun
open Classical SparsePort MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle ItsrLabel
noncomputable section
variable (S : Sha2Set) (ar : ℕ) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (A : QSM_DT_TCR_Adversary (ArityGame.Work E) (ArityGame.Base S ar seeds))
variable (forge : (Port → Words) → A.State → S.Node → Closed (ArityGame.Work E) (ℕ × Arity.Msg S ar))

theorem salted_inner (pk : S.Node) (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    (h : ar ≤ 67) (q : ℕ) (hq : q ≤ 2^100)
    (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) q)
    (post : ∀ st, PUE (spec:=unifSpec) cnt0 (fun H => forge H st pk) (2^41)) :
    uniformMean (fun H : Table => tcrInner (ArityGame.adversary S ar seeds A forge (perm π H)) pk) ≤
      ((2:ℝ≥0∞)^28)⁻¹ + ((2:ℝ≥0∞)^97)⁻¹ := by
  apply conditioned S ar seeds A forge pk π hp he h q hq count post
  exact fun H h' D log => target_ready S pk ar π H h' D log
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.salted_inner
