import Ideal.Realize.WotsRealizers
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))
theorem f1 : (preAdv S oR pkSeedDist).State = Open.RState Link.vp P0 := sorry
theorem f2 : IsQueryBoundP (preAdv S oR pkSeedDist).choose (fun _ => True) 0 := sorry
theorem f3 (A : WotsPreAdv128 pkSeedDist) : A.ChooseBound 0 := sorry
theorem f4 : (preAdv S oR pkSeedDist) = (preAdv S oR pkSeedDist) := sorry
end Ideal.Realize.Wots
