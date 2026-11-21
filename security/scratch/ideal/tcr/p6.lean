import Ideal.Realize.Port
import Ideal.Realize.Phase1
import Ideal.Transport.AdvTcr
import Ideal.ComposeFinal
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Tcr
open Reduction Reduction.Open Ideal.Transport
abbrev P₀ : Primitives Link.vp.params := R₀ dT dH
attribute [local irreducible] Reduction.arityTargets Reduction.tcrTargets
variable (d : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk)
set_option maxHeartbeats 400000
example : TcrP1State Link.vp P₀ = TcrP1State Link.vp (primsG (liftC g)) := rfl
example : TcrP1Spec P₀ n = TcrP1Spec (primsG (liftC g)) n := rfl
example : thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) d n = thashArityProblemT Link.vp (setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g)) d n := rfl
example : thashArityProblemT Link.vp (R₀ (thG g) (hmG g)) d n = thashArityProblemT Link.vp (primsG (liftC g)) d n := rfl
end Ideal.Realize.Tcr
namespace Ideal.Realize.Tcr
set_option pp.explicit true in
example (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) : 𝒟[SM_DT_TCR_Experiment (Reduction.bTcrArM n (S.typedS (optRandU oR) d g))] = 0 := by
  trace_state
  sorry
end Ideal.Realize.Tcr
