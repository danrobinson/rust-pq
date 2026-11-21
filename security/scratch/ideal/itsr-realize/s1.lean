import Ideal.ComposeFinal
import Ideal.Realize.Port
import Ideal.Transport.AdvItsr
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction
namespace Ideal.Realize.Itsr
open Ideal.Transport Ideal.Realize

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

def oR₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) : ProbComp (Bytes 16) :=
  oR pk.pkSeed pk.pkRoot

theorem step_transport (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) :
    Lazy.bItsrL (S.typedS (optRandU oR) d g) =
      Lazy.bItsrL (bytesToTypedS (prims := R₀ (thG g) (hmG g)) (codec := codec₀) (optRand := oR₀ oR)
        (pkSeedDist := d) ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary :=
  bItsrL_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (oR₀ oR) (optRandU oR g) (fun _ => rfl) d
    (fun pk => simulateQ (instImpl g) (S.main pk))

end Ideal.Realize.Itsr
