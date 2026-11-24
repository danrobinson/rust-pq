import Integration.SlhDsaCompressionWotsTransport
import Ideal.Transport.Verify
namespace Reduction.QInd
open SLHDSA SLHDSA.Security Ideal.Transport OracleComp OracleSpec PQ.Interactive Quantum
variable {W : Type} [Fintype W]

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)


variable [DecidableEq prims.AdrsKey] [DecidableEq prims.PkSeed]
variable (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
include hopt in
theorem qMemoForge_tr (n : ℕ) (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed) :
    qMemoForge n (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)) st pk =
      qMemoForge n (qPureBytesToInternal B) st pk := by
  let key := idealPk vp prims st.1 pk
  let key' := trPk prims.core prf pm key
  let base := g2SignOracle optRand key (fun m R => idealSign vp prims st.1 m key R)
  let target := g2SignOracle (prims := setPrf prims prf pm) optRand' key'
    (fun m R => idealSign vp (setPrf prims prf pm) st.1 m key' R)
  have hs (m) (s : G2Log prims) : (target m).run s = (fun z => (trSig _ prf pm z.1,z.2)) <$> (base m).run s := by
    simp only [base,target,key',g2SignOracle,hopt,idealSign_tr]
    simp
    krfl
  have h := close_qPureBytesToInternal_tr prf pm codec optRand optRand' pkSeedDist id B base target hs key []
  unfold qMemoForge
  rw [idealPk_setPrf]
  simp only [id,base,target,key',key] at h
  rw [h,bind_map_left]
  apply bind_congr
  intro z
  rw [verifyCalls_setPrf,findCollisionM_setPrf,classOut_setPrf]
end Reduction.QInd
#print axioms Reduction.QInd.qMemoForge_tr
