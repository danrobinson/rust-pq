import Ideal.Realize.WotsRealize
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))
example : True := by
  have := (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose
  trivial
example : True := by
  have := @emb_noComp (Bytes 22) ((_ : Unit) × Bytes 22 × List (Bytes 16)) (SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) + collSpecC (Bytes 22) (Bytes 16)) _ (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose
  trivial
example (g : CF St Blk) : True := by
  have := instImpl_emb (X := SM_DT_PRE_challengeSpec (Bytes 22) (Bytes 16) + collSpecC (Bytes 22) (Bytes 16)) g (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose
  trivial
example : True := by
  have := emb_noComp (X := SM_DT_UD_challengeSpec (Bytes 22) (Bytes 16) + collSpecC (Bytes 22) (Bytes 16)) (rUd (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).pick
  trivial
end Ideal.Realize.Wots
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))
theorem tq (h : IsQueryBoundP (rPre (vp := Link.vp) (prims := P0) pkSeedDist (Lazy.bWotsS (dF oR pkSeedDist))).choose isChalI 5) :
    (preAdv S oR pkSeedDist).ChalBound 5 :=
  emb_bound (fun i => (FWotsPre128 pkSeedDist).pIsChal i = true) _ 5 (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI, THFam.pIsChal]) h)
end Ideal.Realize.Wots
