import Ideal.Inst.WotsPre128
import Ideal.Sha.HmsgShape
import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
open OracleComp OracleSpec ENNReal KeyedHash
namespace Ideal
open SLHDSA

theorem hmsg_realCF (R pk root : Bytes 16) (M : List UInt8) :
    (primsG (liftC realCF)).Hmsg R pk root M = Link.prims.Hmsg R pk root M := by
  show sha2HmsgG (liftC realCF) Link.vp.params R pk root M = _
  rw [liftC_realCF]
  rfl

theorem itsrProblem_realCF_hash (R : Bytes 16) (x : Bytes 16 × Bytes 16 × List UInt8) :
    (Reduction.itsrProblem Link.vp (primsG (liftC realCF))).khf.hash R x =
      (Reduction.itsrProblem Link.vp Link.prims).khf.hash R x :=
  hmsg_realCF R x.1 x.2.1 x.2.2
end Ideal
