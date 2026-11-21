import Ideal.Realize.ForsAdv
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction TweakableHash
namespace Ideal.Realize.Fors
open Ideal.Transport Reduction.Open Ideal.Realize
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16)) (g : CF St Blk)

example : (OracleComp (ForsP1Spec P₀) Unit) = OracleComp (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) + SourceFinalValidity.collectionSpec (forsDsprProblem Link.vp (R₀ (thG g) (hmG g)) d).thColl)) Unit := rfl
example : (OracleComp (ForsP1Spec P₀) Unit) = OracleComp (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) + SourceFinalValidity.collectionSpec (forsDsprProblem Link.vp (primsG (liftC g)) d).thColl)) Unit := rfl
example : (OracleComp (ForsP1Spec (R₀ (thG g) (hmG g))) Unit) = OracleComp (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec (Bytes 22) (Bytes 16) (Bytes 16) + SourceFinalValidity.collectionSpec (forsDsprProblem Link.vp (R₀ (thG g) (hmG g)) d).thColl)) Unit := rfl
example : (toDspr (Lazy.bOpenPreS (A₀ S oR d g (thG g) (hmG g)))).State = ForsP1State Link.vp P₀ := rfl
end Ideal.Realize.Fors
