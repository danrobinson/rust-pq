import Ideal.Realize.WotsRealize
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport
variable (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16))
variable (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) (A : Forger Link.vp (R₀ T H) (optRand₀ oR) pkSeedDist)
example : True := by
  have : (rPre (vp := Link.vp) (prims := R₀ T H) pkSeedDist (bWotsS A)).State = Unit := sorry
  trivial
example : True := by
  have : (rPre (vp := Link.vp) (prims := R₀ T H) pkSeedDist (bWotsS A)).choose = (rPre (vp := Link.vp) (prims := R₀ T H) pkSeedDist (bWotsS A)).choose := sorry
  trivial
example : True := by
  have : IsQueryBoundP (rPre (vp := Link.vp) (prims := R₀ T H) pkSeedDist (bWotsS A)).choose (fun _ => True) 5 := sorry
  trivial
example : True := by
  have : IsQueryBoundP (rPre (vp := Link.vp) (prims := R₀ T H) pkSeedDist (bWotsS A)).choose isChalI 5 := by exact sorry
  trivial
end Ideal.Realize.Wots
