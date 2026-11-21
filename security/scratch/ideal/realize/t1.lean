import Ideal.Core.SimLemmas
import Ideal.Sha.HmsgShape
import Ideal.Sha.HmacShape
import Reduction.Open.WithHash
open OracleComp OracleSpec SLHDSA SLHDSA.Security
namespace Ideal.Realize
abbrev CSpec := unifSpec + hS St Blk

def thG (g : CF St Blk) : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 :=
  sha2ThashG (liftC g) Link.vp.params
def hmG (g : CF St Blk) : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30 :=
  sha2HmsgG (liftC g) Link.vp.params
def prfG (g : CF St Blk) : Bytes 16 → Bytes 16 → Adrs → Bytes 16 :=
  fun pkSeed skSeed address => checkedNodeOrZero (sha2PRFCheckedG (liftC g) pkSeed skSeed address)
def pmG (g : CF St Blk) : Bytes 16 → Bytes 16 → List Byte → Bytes 16 :=
  sha2PRFmsgG (liftC g)

abbrev primsQ (g : CF St Blk) : Primitives Link.vp.params :=
  Reduction.Open.withTH Link.prims (thG g) (hmG g)

theorem thG_shape (g : CF St Blk) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    thG g pk a xs = out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) :=
  primsG_Thash_shape g pk a xs

theorem hmG_shape (g : CF St Blk) (R pk root : Bytes 16) (M : List UInt8) :
    hmG g R pk root M =
      dig30 (mdFold g IV128 (oblocksH R pk (mdFold g IV128 (iblocksH R pk root M)))) :=
  hmsg_shape g R pk root M

theorem pmG_shape (g : CF St Blk) (k r : Bytes 16) (M : List UInt8) :
    pmG g k r M =
      out16 (g (g (IV128, okey k), oblock (mdFold g (g (IV128, ikey k)) (iblocks r M)))) :=
  msgPrf_shape g k r M

def hashC : QueryImpl (publicHashSpec Link.prims.core) (OracleComp CSpec)
  | .thash pk a xs => (pure default : OracleComp CSpec (Bytes 16))
  | .hmsg R pk root M => (pure default : OracleComp CSpec (Bytes 30))
end Ideal.Realize
