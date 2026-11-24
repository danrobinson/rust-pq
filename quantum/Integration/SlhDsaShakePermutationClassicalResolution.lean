import Integration.SlhDsaShakePermutationClassicalCoins
import PQ.Interactive.QromBridgeEval

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp PQ.Interactive
noncomputable section
variable {ι Z : Type} {sp : OracleSpec ι} [∀ i, Fintype (sp.Range i)]

theorem resolved_count (P : OracleComp (unifSpec + sp) Z) (w : ι → ℕ) (q : ℕ)
    (hq : WCount (Sum.elim (fun _ => 0) w) P q) (c : (resolve P).Coins) :
    WCount w ((resolve P).run c) q := by
  induction P using OracleComp.recOn generalizing q with
  | pure z => exact trivial
  | queryBind i k ih =>
    rcases i with n|i
    · change Fin (n+1) × ((r : Fin (n+1)) → (resolve (k r)).Coins) at c
      apply ih c.1 q _ (c.2 c.1)
      exact hq.2 _
    · change (r : sp.Range i) → (resolve (k r)).Coins at c
      change w i ≤ q ∧ ∀ r, WCount w ((resolve (k r)).run (c r)) (q-w i)
      exact ⟨hq.1,fun r => ih r _ (hq.2 r) (c r)⟩
end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.resolved_count
