import Ideal.Realize.Port
import Ideal.Realize.Phase1
import Ideal.Transport.AdvWots
import Ideal.ComposeFinal
import Reduction.Open.Wots
import Reduction.Open.WotsCountsSM

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Wots
open Reduction Ideal.Transport

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

noncomputable def B₀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Forger Link.vp (R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist :=
  (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀) (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
    ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary

theorem stepUd (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    rUd pkSeedDist (Lazy.bWotsS (S.typedS (optRandU oR) pkSeedDist g)) =
      rUd pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g)) :=
  rUd_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))

theorem stepUdE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    rUd pkSeedDist (Lazy.bWotsS (S.typedE (optRandU oR) pkSeedDist g)) =
      rUd pkSeedDist (Lazy.bWotsS (B₀ S oR pkSeedDist g)) :=
  stepUd S oR pkSeedDist g

example (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
   Open.RState Link.vp (primsG (liftC g)) = Open.RState Link.vp (R₀ dT dH) := rfl

example (pkSeedDist : ProbComp (Bytes 16)) : (FWotsPre128 pkSeedDist).padvS =
   unifSpec + (hS St Blk + (SM_DT_UD_challengeSpec (Bytes 22) (Bytes 16) + Open.collSpecC (Bytes 22) (Bytes 16))) := rfl

end Ideal.Realize.Wots
