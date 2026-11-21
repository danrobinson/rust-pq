import Integration.SlhDsaBridgeInd

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Reduction.QMsg
open Ideal.Transport Reduction.QInd

variable {W : Type} [Fintype W]

section Cast
variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable {ι : Type} (G : OracleSpec ι)

/-- A quantum program over the open interface of `setPrf prims prf pm`, read over that of
`prims` (kernel identity). -/
def castQ {α : Type} (x : QOC W (Lazy.OSpec (setPrf prims prf pm) G) α) :
    QOC W (Lazy.OSpec prims G) α := by
  kexact x

theorem castQ_bind {α β : Type} (x : QOC W (Lazy.OSpec (setPrf prims prf pm) G) α)
    (f : α → QOC W (Lazy.OSpec (setPrf prims prf pm) G) β) :
    castQ prims prf pm G (x >>= f) = castQ prims prf pm G x >>= fun a => castQ prims prf pm G (f a) := by
  krfl

variable [DecidableEq prims.Y] [SampleableType prims.Y]

theorem qLazyRun_setPrf {α : Type} (X : QOC W (Lazy.OSpec (setPrf prims prf pm) G) α) :
    qLazyRun (PublicHash.impl (setPrf prims prf pm)) X =
      qLazyRun (PublicHash.impl prims) (castQ prims prf pm G X) := by krfl

end Cast

section Msg
variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)

include hopt in
theorem qMsgOpenW_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    castQ prims prf pm (Lazy.msgG prims)
        (qMsgOpenW (prims := setPrf prims prf pm) sufCheck
          (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B))) =
      qMsgOpenW sufCheck (qPureBytesToInternal B) := by
  unfold qMsgOpenW
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun pkSeed => ?_
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun root => ?_
  rw [castQ_bind]
  have h := qRunForgerSig_tr prf pm codec optRand optRand' pkSeedDist B ⟨pkSeed, root⟩
    (fun m => castO' prims prf pm (Lazy.msgG prims) (Lazy.msgSignO optRand ⟨pkSeed, root⟩ m))
    (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩))
    (fun m => msgSignO_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ m)
  have h2 : castQ prims prf pm (Lazy.msgG prims)
      (qRunForgerSig (prims := setPrf prims prf pm)
        (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B))
        ⟨pkSeed, root⟩ (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' ⟨pkSeed, root⟩)) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        qRunForgerSig (qPureBytesToInternal B) ⟨pkSeed, root⟩
          (Lazy.msgSignO optRand ⟨pkSeed, root⟩) := by
    have h' := congrArg (castQ prims prf pm (Lazy.msgG prims)) h
    exact h'.trans (by krfl)
  refine (bind_congr_k h2 fun z => rfl).trans ?_
  rw [bind_map_left]
  refine bind_congr fun z => ?_
  have hv := sufCheck_setPrf prims prf pm ⟨pkSeed, root⟩ z.1 z.2
  simp only [trPk_mk] at hv
  rw [hv]
  show _ = _
  krfl

include hopt in
theorem qbPrfMsgWL_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrfMsgWL (prims := setPrf prims prf pm) sufCheck
        (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)) =
      qbPrfMsgWL sufCheck (qPureBytesToInternal B) := by
  unfold qbPrfMsgWL
  rw [qLazyRun_setPrf prims prf pm (Lazy.msgG prims),
    qMsgOpenW_setPrf prf pm codec optRand optRand' hopt pkSeedDist B]

end Msg
end Reduction.QMsg
