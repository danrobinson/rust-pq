import Ideal.Realize.WotsRealizers
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))
attribute [local irreducible] dF in
theorem x1 : (preAdv S oR pkSeedDist).ChooseBound 0 := by
  unfold PreAdv.ChooseBound
  exact genP_q1 _ _
end Ideal.Realize.Wots
