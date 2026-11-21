import Ideal.Transport.AdvLazy
import Reduction.Lazy.SufMsgLazy

/-!
# Core-invariance of the `PRF_msg` distinguishers `Lazy.bPrfMsgL A`, `Lazy.bPrfMsgWL sufCheck A`
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction

set_option linter.unusedSectionVars false

section Msg

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)
  (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))

set_option quotPrecheck false in
/-- The typed forger over `prims` built from the byte-level main `S`. -/
local notation "Abase" =>
  (bytesToTyped (prims := prims) (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
    ⟨S⟩)

set_option quotPrecheck false in
/-- The typed forger over `setPrf prims prf pm` built from the same byte-level main `S`. -/
local notation "Aset" =>
  (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
    (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)

include hopt in
/-- The signing procedure of the open `PRF_msg` distinguisher. -/
theorem msgSignO_tr (pk : PublicKeyCore prims.core) (m : List Byte) :
    Lazy.msgSignO (prims := setPrf prims prf pm) optRand' (trPk _ prf pm pk) m =
      trSig _ prf pm <$> castO' prims prf pm (Lazy.msgG prims)
        (Lazy.msgSignO (prims := prims) optRand pk m) := by
  unfold Lazy.msgSignO
  simp only [castO'_bind, castO'_liftM, castO'_gameQ, map_bind, hopt, trPk_pkSeed, trPk_pkRoot]
  simp only [← lazyOpenSign_tr prims prf pm (Lazy.msgG prims)]

include hopt in
/-- The forger run inside the open EUF `PRF_msg` program. -/
theorem msg_run_setPrf (pkSeed : prims.PkSeed) (root : prims.Y) :
    castO prims prf pm (Lazy.msgG prims)
        (runForger (prims := setPrf prims prf pm) Aset ⟨pkSeed, root⟩
          (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' ⟨pkSeed, root⟩)) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        runForger Abase ⟨pkSeed, root⟩ (Lazy.msgSignO optRand ⟨pkSeed, root⟩) := by
  kexact lazy_runForger_tr prims prf pm (Lazy.msgG prims) codec optRand optRand'
    pkSeedDist S ⟨pkSeed, root⟩ (Lazy.msgSignO optRand ⟨pkSeed, root⟩)
    (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩))
    (fun m => msgSignO_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ m)

include hopt in
/-- The forger run inside the open SUF `PRF_msg` program. -/
theorem msgW_run_setPrf (pkSeed : prims.PkSeed) (root : prims.Y) :
    castO prims prf pm (Lazy.msgG prims)
        (runForgerSig (prims := setPrf prims prf pm) Aset ⟨pkSeed, root⟩
          (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' ⟨pkSeed, root⟩)) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        runForgerSig Abase ⟨pkSeed, root⟩ (Lazy.msgSignO optRand ⟨pkSeed, root⟩) := by
  kexact lazy_runForgerSig_tr prims prf pm (Lazy.msgG prims) codec optRand optRand'
    pkSeedDist S ⟨pkSeed, root⟩ (Lazy.msgSignO optRand ⟨pkSeed, root⟩)
    (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩))
    (fun m => msgSignO_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ m)

include hopt in
/-- The open EUF `PRF_msg` program. -/
theorem msgOpen_setPrf :
    castO prims prf pm (Lazy.msgG prims) (Lazy.msgOpen Aset) = Lazy.msgOpen Abase := by
  unfold Lazy.msgOpen
  simp only [castO_bind, castO_liftM, castO_pure,
    msg_run_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S, bind_map_left]
  have hv : ∀ (pkSeed : prims.PkSeed) (root : prims.Y) msgs msg sig,
      harnessValid (prims := setPrf prims prf pm) ⟨pkSeed, root⟩ msgs msg (trSig _ prf pm sig) =
        harnessValid (prims := prims) ⟨pkSeed, root⟩ msgs msg sig :=
    fun pkSeed root => harnessValid_setPrf prims prf pm ⟨pkSeed, root⟩
  simp only [hv]
  show _ = _
  krfl

include hopt in
/-- The open SUF `PRF_msg` program. -/
theorem msgOpenW_setPrf :
    castO prims prf pm (Lazy.msgG prims)
        (Lazy.msgOpenW (sufCheck (prims := setPrf prims prf pm)) Aset) =
      Lazy.msgOpenW sufCheck Abase := by
  unfold Lazy.msgOpenW
  simp only [castO_bind, castO_liftM, castO_pure,
    msgW_run_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S, bind_map_left]
  have hv : ∀ (pkSeed : prims.PkSeed) (root : prims.Y)
      (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims),
      sufCheck (prims := setPrf prims prf pm) ⟨pkSeed, root⟩ (f.1, trSig _ prf pm f.2)
          (trLog prf pm log) = sufCheck (prims := prims) ⟨pkSeed, root⟩ f log :=
    fun pkSeed root => sufCheck_setPrf prims prf pm ⟨pkSeed, root⟩
  simp only [hv]
  show _ = _
  krfl

include hopt in
/-- **The EUF `PRF_msg` distinguisher over `setPrf prims prf pm` is the one over `prims`.** -/
theorem bPrfMsgL_setPrf : Lazy.bPrfMsgL Aset = Lazy.bPrfMsgL Abase := by
  unfold Lazy.bPrfMsgL
  rw [lazyRun_setPrf, msgOpen_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S]

include hopt in
/-- **The SUF `PRF_msg` distinguisher over `setPrf prims prf pm` is the one over `prims`.** -/
theorem bPrfMsgWL_setPrf :
    Lazy.bPrfMsgWL (sufCheck (prims := setPrf prims prf pm)) Aset =
      Lazy.bPrfMsgWL sufCheck Abase := by
  unfold Lazy.bPrfMsgWL
  rw [lazyRun_setPrf, msgOpenW_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S]

include hopt in
/-- The SUF distinguisher at the strong forger wrapper. -/
theorem bPrfMsgWL_setPrf_S :
    Lazy.bPrfMsgWL (sufCheck (prims := setPrf prims prf pm))
        (bytesToTypedS (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary =
      Lazy.bPrfMsgWL sufCheck (bytesToTypedS (prims := prims) (codec := codec)
        (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary :=
  bPrfMsgWL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

include hopt in
/-- Real experiment of the EUF distinguisher, against any `PRF_msg` candidate `P` (in
particular `msgPrf vp (setPrf prims prf pm)`, whose `eval` is `pm`). -/
theorem bPrfMsgL_real_setPrf {K : Type} (P : PRFScheme K (prims.Y × List Byte) prims.Y) :
    P.prfRealExperiment (Lazy.bPrfMsgL (prims := setPrf prims prf pm) Aset) = P.prfRealExperiment (Lazy.bPrfMsgL Abase) :=
  congrArg P.prfRealExperiment
    (bPrfMsgL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- Ideal experiment of the EUF distinguisher. -/
theorem bPrfMsgL_ideal_setPrf :
    PRFScheme.prfIdealExperiment (Lazy.bPrfMsgL Aset) =
      PRFScheme.prfIdealExperiment (Lazy.bPrfMsgL Abase) :=
  congrArg PRFScheme.prfIdealExperiment
    (bPrfMsgL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- Real experiment of the SUF distinguisher, against any `PRF_msg` candidate `P`. -/
theorem bPrfMsgWL_real_setPrf {K : Type} (P : PRFScheme K (prims.Y × List Byte) prims.Y) :
    P.prfRealExperiment
        (Lazy.bPrfMsgWL (prims := setPrf prims prf pm) (sufCheck (prims := setPrf prims prf pm)) Aset) =
      P.prfRealExperiment (Lazy.bPrfMsgWL sufCheck Abase) :=
  congrArg P.prfRealExperiment
    (bPrfMsgWL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- Ideal experiment of the SUF distinguisher. -/
theorem bPrfMsgWL_ideal_setPrf :
    PRFScheme.prfIdealExperiment
        (Lazy.bPrfMsgWL (sufCheck (prims := setPrf prims prf pm)) Aset) =
      PRFScheme.prfIdealExperiment (Lazy.bPrfMsgWL sufCheck Abase) :=
  congrArg PRFScheme.prfIdealExperiment
    (bPrfMsgWL_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

end Msg

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms msgSignO_tr
#print axioms msgOpen_setPrf
#print axioms msgOpenW_setPrf
#print axioms bPrfMsgL_setPrf
#print axioms bPrfMsgWL_setPrf
#print axioms bPrfMsgWL_setPrf_S
#print axioms bPrfMsgL_real_setPrf
#print axioms bPrfMsgL_ideal_setPrf
#print axioms bPrfMsgWL_real_setPrf
#print axioms bPrfMsgWL_ideal_setPrf
end AxiomCheck
