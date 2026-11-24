import Integration.SlhDsaBridgeMachFors
import Integration.SlhDsaCompressionForsTransport
import Integration.SlhDsaBridgeMachItsr2
import Ideal.Transport.AdvWots

namespace Reduction.QInd
open SLHDSA SLHDSA.Security Ideal.Transport OracleComp OracleSpec PQ.Interactive Quantum
variable {W : Type} [Fintype W]

private theorem close_wrap0 {ι ι' τ α : Type} {sp : OracleSpec ι} {sp' : OracleSpec ι'}
    (h : QueryImpl sp (OracleComp (unifSpec + sp')))
    (impl : QueryImpl (unifSpec + sp') (StateT τ ProbComp)) (P : QOC W sp α) (s : τ) :
    close impl (wrap0 h P) s = close (fun t => simulateQ impl (h t)) P s := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j|q
    · rw [wrap0_instr_bind,close_instr_bind,close_instr_bind]
      simp only [ih]
    · rw [wrap0_query_bind,close_bind,close_liftQ,close_query_bind]
      exact bind_congr fun x => ih x.1 x.2

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

theorem close_qPureBytesToInternal_tr {σ σ' : Type} (f : σ → σ')
    (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (impl : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT σ ProbComp))
    (impl' : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm))
      (StateT σ' ProbComp))
    (h : ∀ m s, (impl' m).run (f s) = (fun z => (trSig _ prf pm z.1, f z.2)) <$> (impl m).run s)
    (pk : PublicKeyCore prims.core) (s : σ) :
    close ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT σ' ProbComp) + impl')
        ((qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)).main
          (trPk _ prf pm pk)) (f s) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), f z.2)) <$>
        close ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT σ ProbComp) + impl)
          ((qPureBytesToInternal B).main pk) s := by
  unfold qPureBytesToInternal qToInternal qPureBytesToTyped QForger.wrapForger trB
  dsimp only
  simp only [wrap0_map, wrap0_wrap0, close_map_out, close_wrap0]
  have hpk : (pureBytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand'
      pkSeedDist).encPk (trPk _ prf pm pk) = (pureBytesView vp prims codec optRand pkSeedDist).encPk pk :=
    encodePublicKey_tr _ prf pm codec pk
  rw [hpk, close_map_state _ _ f ?_]
  · simp only [Functor.map_map]
    congr 1
    funext z
    exact Prod.ext (readForgery_pure_tr prf pm codec optRand optRand' pkSeedDist z.1) rfl
  · intro t s
    rcases t with n | mc
    · simp [Coded.signingImpl, Guarded.signingImpl]
    · simp only [Coded.signingImpl, simulateQ_map]
      simp only [simulateQ_HasQuery_query, Guarded.signingImpl]
      cases pureEncode mc with
      | error x => simp [pureBytesView, encodePureSig]; rfl
      | ok m =>
        simp only [simulateQ_map, simulateQ_HasQuery_query, QueryImpl.add_apply_inr, StateT.run_map,
          h, Functor.map_map]
        simp only [pureBytesView, encodePureSig]
        congr 1
        funext a
        exact Prod.ext (congrArg some (encodeSignature_tr vp _ prf pm codec a.1)) rfl

variable [DecidableEq prims.AdrsKey] [DecidableEq prims.PkSeed]
variable (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)

include hopt in
theorem qWotsForge_tr (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (st : Open.WState vp prims) (pk : prims.PkSeed) :
    qWotsForge (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)) st pk =
      qWotsForge (qPureBytesToInternal B) st pk := by
  let key : PublicKeyCore prims.core := ⟨pk,st.2.2⟩
  let base := g2SignOracle optRand key (signFromHist st.1 st.2.1 key)
  let key' := trPk prims.core prf pm key
  let target := g2SignOracle (prims := setPrf prims prf pm) optRand' key' (signFromHist (prims := setPrf prims prf pm) st.1 st.2.1 key')
  have hs (m) (s : G2Log prims) : (target m).run s = (fun z => (trSig _ prf pm z.1,z.2)) <$> (base m).run s := by
    simp only [base, target, key', g2SignOracle, hopt, signFromHist_tr]
    simp
    krfl
  have h := close_qPureBytesToInternal_tr prf pm codec optRand optRand' pkSeedDist id B base target hs key []
  unfold qWotsForge
  simp only [id,base,target,key',key,trPk_mk] at h
  rw [h,bind_map_left]
  apply bind_congr
  intro z
  exact congrArg (fun v => (liftU (pure v) : Closed W _)) (wotsAnswer_setPrf prims prf pm st.1 st.2.1 key z.1.1 z.1.2)

end Reduction.QInd
#print axioms Reduction.QInd.qWotsForge_tr
