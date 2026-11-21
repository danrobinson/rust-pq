import PQ.Interactive.QromBridgeTcr
import PQ.QROM.PreGiven

open OracleComp OracleSpec ENNReal Quantum MeasureTheory TweakableHash

namespace PQ.Interactive
variable {ι PkSeed Tw M M' Y : Type} [DecidableEq Tw] [SampleableType M']

example (P : SM_DT_PRE_Problem ι PkSeed Tw M M' Y) (pk : PkSeed) (t : Tw) (L : List (Tw × M')) (C : List Tw)
  (hc : ¬ (P.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t)) :
  (SM_DT_PRE_challengeOracle P pk t).run (L, C) = (($ᵗ M' : ProbComp M') >>= fun x ↦ pure (some (P.th.eval pk t (P.emb x)), (L ++ [(t, x)], C))) := by
  simp [SM_DT_PRE_challengeOracle, hc]
  
end PQ.Interactive
