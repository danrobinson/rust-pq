import Ideal.Realize.ItsrCount
import Ideal.Transport.Core
open OracleComp OracleSpec SLHDSA SLHDSA.Security KeyedHash
namespace Ideal.Realize.Itsr
open Reduction Reduction.Lazy Ideal.Realize Ideal.Itsr

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl
def oR₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp (Bytes 16) :=
  oR pk.pkSeed pk.pkRoot

set_option maxHeartbeats 400000 in
theorem t1 (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) (S : ForgerI) (oR) (d : ProbComp (Bytes 16)) :
    itsrOpenP (prims := R₀ T H) (oR₀ oR) d (typedP codec₀ S.main) =
      itsrOpenP (prims := R₀ dT dH) (oR₀ oR) d (typedP codec₀ S.main) := by
  krfl
end Ideal.Realize.Itsr
