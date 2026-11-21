import Ideal.Transport.Core
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction Ideal.Transport
variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y) (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
example (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    idealRoot vp (setPrf prims prf pm) tbl pk = idealRoot vp prims tbl pk := by krfl
example (n : ℕ) (L : List (prims.AdrsKey × List prims.Y)) (jm : ℕ × List prims.Y) :
    classOut (setPrf prims prf pm) n L jm = classOut prims n L jm := by krfl
example (pk : prims.PkSeed) (t c : List (prims.AdrsKey × List prims.Y)) :
    findCollisionM (prims := setPrf prims prf pm) pk t c = findCollisionM (prims := prims) pk t c := by krfl
example (tbl : SecretTable vp prims) (m : List Byte) (pk : PublicKeyCore prims.core) (R : prims.Y) :
    idealSign vp (setPrf prims prf pm) tbl m (trPk _ prf pm pk) R = trSig _ prf pm (idealSign vp prims tbl m pk R) := by krfl
example (pk : PublicKeyCore prims.core) (m : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    verifyCalls (prims := setPrf prims prf pm) (trPk _ prf pm pk) m (trSig _ prf pm sig) = verifyCalls pk m sig := by krfl
