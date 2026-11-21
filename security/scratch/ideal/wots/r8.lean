import Ideal.Realize.WotsRealizers
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))
set_option linter.constructorNameAsVariable false
theorem y0 (h : @IsQueryBoundP _ (udSpecC P0.AdrsKey P0.Y) _ (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose isChalI _ 5) : (preAdv S oR pkSeedDist).ChalBound 5 :=
  genP_chal (FWotsPre128 pkSeedDist) _ 5 h
theorem y3 (h : @IsQueryBoundP _ (udSpecC P0.AdrsKey P0.Y) _ (rUd (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).pick isChalI _ 5) : (udAdv S oR pkSeedDist).ChalBound 5 :=
  genP_chal (FWotsPre128 pkSeedDist) _ 5 h
end Ideal.Realize.Wots
