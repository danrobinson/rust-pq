import Integration.SlhDsaBridgeInd
import Ideal.Transport.AdvFors

namespace Reduction.QInd
open SLHDSA SLHDSA.Security Ideal.Transport OracleComp OracleSpec PQ.Interactive Quantum
variable {vp : ValidatedParams} {prims : Primitives vp.params} {W : Type} [Fintype W]
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (seeds : ProbComp prims.PkSeed) (B : QForger W (pureBytesAlg vp prims codec optRand seeds))

include hopt in
theorem qRunForgerLog_tr {ι : Type} {spec : OracleSpec ι} (pk : PublicKeyCore prims.core)
    (rnd : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (sign : List Byte → prims.Y → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte → prims.Y → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m R, sign' m R = trSig _ prf pm <$> sign m R) :
    qRunForgerLog (qPureBytesToInternal (trB prf pm codec optRand optRand' seeds B))
        (trPk _ prf pm pk) rnd sign' =
      (fun z => ((z.1.1,trSig _ prf pm z.1.2),z.2)) <$> qRunForgerLog (qPureBytesToInternal B) pk rnd sign := by
  unfold qRunForgerLog
  refine wrap_qPureBytesToInternal_tr prf pm codec optRand optRand' seeds id B _ _ ?_ pk []
  intro m s
  simp only [logSignOracle, hopt, hs, id]
  simp

variable [DecidableEq prims.AdrsKey] [DecidableEq prims.PkSeed]
include hopt in
theorem qFindRun_tr (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pk : prims.PkSeed) :
    qFindRun (qPureBytesToInternal (trB prf pm codec optRand optRand' seeds B)) st pk =
      qFindRun (qPureBytesToInternal B) st pk := by
  unfold qFindRun
  congr 1
  unfold qOpenPreFind
  rw [idealPk_setPrf]
  have hr : (lazyRandomizerLift (prims := setPrf prims prf pm) :
      G2Log prims → List Byte → prims.Y → OracleComp (openSpecY prims) prims.Y) =
      lazyRandomizerLift (prims := prims) := by krfl
  rw [hr, qRunForgerLog_tr prf pm codec optRand optRand' hopt seeds B _ _ _ _
    (fun m R => openSign_setPrf prims prf pm _ st.1 st.2.2 m R), bind_map_left]
  apply bind_congr
  intro z
  rw [openPreAnswer_setPrf]

end Reduction.QInd
#print axioms Reduction.QInd.qFindRun_tr
