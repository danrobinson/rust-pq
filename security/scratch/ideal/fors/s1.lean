import Ideal.Realize.Port
import Ideal.Realize.Phase1
import Ideal.Transport.AdvFors
import Ideal.ComposeFinal
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction
namespace Ideal.Realize.Fors
open Ideal.Transport Reduction.Open Ideal.Realize

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

theorem primsG_eq (g : CF St Blk) :
    primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) := rfl

theorem codecG_eq (g : CF St Blk) :
    codecG g = trCodec core₀ (prfG g) (pmG g) codec₀ := rfl

def oR₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) :
    PublicKeyCore (R₀ T H).core → ProbComp (R₀ T H).Y := fun pk => oR pk.pkSeed pk.pkRoot

theorem step1 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.toDspr (Reduction.Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)) =
      Reduction.toDspr (Reduction.Lazy.bOpenPreS (bytesToTypedS (prims := R₀ (thG g) (hmG g))
        (codec := codec₀) (optRand := oR₀ oR (thG g) (hmG g)) (pkSeedDist := pkSeedDist)
        ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary) :=
  toDspr_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (oR₀ oR (thG g) (hmG g))
    (optRandU oR g) (fun _ => rfl) pkSeedDist _

end Ideal.Realize.Fors
#print axioms Ideal.Realize.Fors.step1
