import Ideal.Realize.WotsRealize
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem udAdv_q1 : (udAdv S oR pkSeedDist).PickBound 0 := by
  unfold UdAdv.PickBound udAdv
  exact emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.pIsH]) _

theorem udAdv_chal : (udAdv S oR pkSeedDist).ChalBound
    ((wotsInsts Link.vp).length * (Link.vp.params.len * 1)) := by
  unfold UdAdv.ChalBound udAdv
  exact emb_bound _ _ _ (IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | t | t <;> simp_all [embIdx, isChalI, THFam.pIsChal])
    (rUd_pick_chal (vp := Link.vp) (prims := P0) pkSeedDist (dF oR pkSeedDist)))
end Ideal.Realize.Wots
