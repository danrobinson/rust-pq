import Ideal.Realize.WotsRealizers
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))
example : (preAdv S oR pkSeedDist).State = Open.RState Link.vp P0 := rfl
example : (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).State = Open.RState Link.vp P0 := rfl
example : (FWotsPre128 pkSeedDist).padvS = unifSpec + (hS St Blk + (SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) + (FWotsPre128 pkSeedDist).collS)) := rfl
set_option linter.constructorNameAsVariable false
theorem x2 (h : IsQueryBoundP (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose isChalI 5) : (preAdv S oR pkSeedDist).ChalBound 5 :=
  genP_chal (FWotsPre128 pkSeedDist) _ 5 h
theorem x3 (h : IsQueryBoundP (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose isChalI 5) : (preAdv S oR pkSeedDist).ChalBound 5 := by
  kexact genP_chal (FWotsPre128 pkSeedDist) _ 5 h
end Ideal.Realize.Wots
