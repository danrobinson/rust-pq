import Reduction.Gen.Forger
import Reduction.Gen.GamePrf
import Reduction.Gen.GameItsr
import Reduction.Lazy.MsgLazy
import Reduction.Lazy.SufMsgLazy
import Reduction.Lazy.ItsrLazy

/-!
# The lazy single-phase adversaries around a general-spec forger

`Lazy.bPrfMsgL`, `Lazy.bPrfMsgWL`, `Lazy.bItsrL` are `lazyRun (PublicHash.impl prims) P` for an
open program `P` (`msgOpen A`, `msgOpenW w A`, `itsrOpen A`) containing one harness run of the
forger.  Here:

* `lazyRunG ds hI P = Prod.fst <$> runGO ds (lazyImpl hI) P []` — the lazy cache handler
  (`Lazy.lazyImpl`, which is `lazyRun` by `Lazy.lazyRun_eq`) around a general-spec open program;
* `msgOpenG`, `msgOpenWG`, `itsrOpenG` — the open programs, the forger being run by `runGO` with
  the harness handler of `runForger` / `runForgerSig` / `runForgerLog`;
* `bPrfMsgLG`, `bPrfMsgWLG`, `bItsrLG`, their naturality (`…_embed`) and linearity (`isLin_…`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]

/-! ## The general lazy run -/

section LazyRun

variable {ι κh : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κh} {D V α : Type}
  [DecidableEq D] [SampleableType V]

/-- `Lazy.lazyRun` for an open program over the general sampling interface. -/
noncomputable def lazyRunG (hI : QueryImpl hspec Id)
    (P : OracleComp ((ds + unifSpec) + (gspec + ((D →ₒ V) + hspec))) α) :
    OracleComp ((ds + unifSpec) + gspec) α :=
  Prod.fst <$> runGO ds (Lazy.lazyImpl hI) P []

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- On a `ds`-free open program, `lazyRunG` is `lazyRun`. -/
theorem lazyRunG_embed (hI : QueryImpl hspec Id)
    (P : OracleComp (Lazy.RSpec gspec D V hspec) α) :
    lazyRunG ds hI (embed ds P) = embed ds (Lazy.lazyRun hI P) := by
  rw [lazyRunG, runGO_embed, Lazy.lazyRun_eq, StateT.run'_eq, embed_map]

end LazyRun

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-! ## Open programs -/

/-- `Lazy.msgOpen` around a general-spec forger family. -/
noncomputable def msgOpenG (F : GFam ds vp prims) :
    OracleComp ((ds + unifSpec) +
      (Lazy.msgG prims + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))) Bool :=
  embed ds (liftM pkSeedDist : OracleComp (Lazy.OSpec prims (Lazy.msgG prims)) prims.PkSeed) >>=
    fun pkSeed ↦ embed ds (Lazy.openKeygen prims (Lazy.msgG prims) pkSeed) >>= fun root ↦
      runGO ds
        ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (Lazy.msgG prims)))).liftTarget
            (StateT (List (List Byte)) (OracleComp (Lazy.OSpec prims (Lazy.msgG prims)))) +
          harnessSignOracle (Lazy.msgSignO optRand ⟨pkSeed, root⟩))
        (F ⟨pkSeed, root⟩) [] >>= fun z ↦
        pure (harnessValid ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2)

/-- `Lazy.msgOpenW` around a general-spec forger family. -/
noncomputable def msgOpenWG (w : WinCheck vp prims) (F : GFam ds vp prims) :
    OracleComp ((ds + unifSpec) +
      (Lazy.msgG prims + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))) Bool :=
  embed ds (liftM pkSeedDist : OracleComp (Lazy.OSpec prims (Lazy.msgG prims)) prims.PkSeed) >>=
    fun pkSeed ↦ embed ds (Lazy.openKeygen prims (Lazy.msgG prims) pkSeed) >>= fun root ↦
      runGO ds
        ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (Lazy.msgG prims)))).liftTarget
            (StateT (SigLog vp prims) (OracleComp (Lazy.OSpec prims (Lazy.msgG prims)))) +
          sigSignOracle (Lazy.msgSignO optRand ⟨pkSeed, root⟩))
        (F ⟨pkSeed, root⟩) [] >>= fun z ↦
        pure (w ⟨pkSeed, root⟩ z.1 z.2)

/-- `Lazy.itsrOpen` around a general-spec forger family. -/
noncomputable def itsrOpenG (F : GFam ds vp prims) :
    OracleComp ((ds + unifSpec) +
      (Lazy.itsrG prims + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core)))
      (prims.Y × ItsrIn prims) :=
  embed ds (liftM pkSeedDist : OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)) prims.PkSeed) >>=
    fun pkSeed ↦ embed ds (Lazy.openKeygen prims (Lazy.itsrG prims) pkSeed) >>= fun root ↦
      runGO ds
        ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))).liftTarget
            (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))) +
          logSignOracle optRand ⟨pkSeed, root⟩ (Lazy.itsrRandomizerO pkSeed root)
            (fun m R ↦ Lazy.openSign prims (Lazy.itsrG prims) m pkSeed root R))
        (F ⟨pkSeed, root⟩) [] >>= fun z ↦
        pure (z.1.2.randomness, (pkSeed, root, z.1.1))

/-! ## The adversaries -/

/-- **`Lazy.bPrfMsgL` around a general-spec forger.** -/
noncomputable def bPrfMsgLG (F : GFam ds vp prims) :
    PRFAdversaryG ds (prims.Y × List Byte) prims.Y :=
  lazyRunG ds (PublicHash.impl prims) (msgOpenG ds optRand pkSeedDist F)

/-- **`Lazy.bPrfMsgWL w` around a general-spec forger.** -/
noncomputable def bPrfMsgWLG (w : WinCheck vp prims) (F : GFam ds vp prims) :
    PRFAdversaryG ds (prims.Y × List Byte) prims.Y :=
  lazyRunG ds (PublicHash.impl prims) (msgOpenWG ds optRand pkSeedDist w F)

/-- **`Lazy.bItsrL` around a general-spec forger.** -/
noncomputable def bItsrLG (F : GFam ds vp prims) : ITSRAdversaryG ds (itsrProblem vp prims) where
  main := lazyRunG ds (PublicHash.impl prims) (itsrOpenG ds optRand pkSeedDist F)

variable {optRand pkSeedDist}

/-! ## Naturality -/

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem msgOpenG_embed (A : Forger vp prims optRand pkSeedDist) :
    msgOpenG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      embed ds (Lazy.msgOpen A) := by
  simp only [msgOpenG, Lazy.msgOpen, runForger, runGO_embed, embed_bind, embed_pure]

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem msgOpenWG_embed (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    msgOpenWG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk)) =
      embed ds (Lazy.msgOpenW w A) := by
  simp only [msgOpenWG, Lazy.msgOpenW, runForgerSig, runGO_embed, embed_bind, embed_pure]

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem itsrOpenG_embed (A : Forger vp prims optRand pkSeedDist) :
    itsrOpenG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      embed ds (Lazy.itsrOpen A) := by
  simp only [itsrOpenG, Lazy.itsrOpen, runForgerLog, runGO_embed, embed_bind, embed_pure]

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `bPrfMsgLG` is `Lazy.bPrfMsgL`. -/
theorem bPrfMsgLG_embed (A : Forger vp prims optRand pkSeedDist) :
    bPrfMsgLG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      embed ds (Lazy.bPrfMsgL A) := by
  rw [bPrfMsgLG, msgOpenG_embed, lazyRunG_embed]; rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `bPrfMsgWLG` is `Lazy.bPrfMsgWL`. -/
theorem bPrfMsgWLG_embed (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    bPrfMsgWLG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk)) =
      embed ds (Lazy.bPrfMsgWL w A) := by
  rw [bPrfMsgWLG, msgOpenWG_embed, lazyRunG_embed]; rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `bItsrLG` is `Lazy.bItsrL`. -/
theorem bItsrLG_embed (A : Forger vp prims optRand pkSeedDist) :
    bItsrLG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      ITSRAdversaryG.ofClassical ds (Lazy.bItsrL A) := by
  unfold bItsrLG ITSRAdversaryG.ofClassical
  rw [itsrOpenG_embed, lazyRunG_embed]; rfl

/-! ## Linearity -/

section Linearity

variable {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
  (w' : QueryImpl (unifSpec + X')
    (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
  (e : PublicKeyCore prims.core → PK')
  (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core)

/-- **Linearity**, real world of the `PRF_msg` game, `bPrfMsgLG`. -/
theorem isLin_bPrfMsgLG_real :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfRealPrG ds (msgPrf vp prims)
        (bPrfMsgLG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold prfRealPrG prfRealExperimentG bPrfMsgLG lazyRunG msgOpenG
  refine isLin_liftR_bind ds _ _ fun k ↦ ?_
  simp only [runGO_bind, runGO_embed, runGO_runGO, runGO_wrapFam, runGO_pure, runG_bind,
    runG_embedO, runG_runGO, runG_pure, bind_assoc, bind_map_left, map_bind, map_pure]
  refine isLin_liftR_bind ds _ _ fun y ↦ ?_
  refine isLin_liftR_bind ds _ _ fun y' ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity**, ideal world of the `PRF_msg` game, `bPrfMsgLG`. -/
theorem isLin_bPrfMsgLG_ideal :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfIdealPrG ds (bPrfMsgLG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold prfIdealPrG prfIdealExperimentG bPrfMsgLG lazyRunG msgOpenG
  simp only [runGO_bind, runGO_embed, runGO_runGO, runGO_wrapFam, runGO_pure, runG_bind,
    runG_embedO, runG_runGO, runG_pure, bind_assoc, bind_map_left, map_bind, map_pure]
  refine isLin_liftR_bind ds _ _ fun y ↦ ?_
  refine isLin_liftR_bind ds _ _ fun y' ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity**, real world of the `PRF_msg` game, `bPrfMsgWLG`. -/
theorem isLin_bPrfMsgWLG_real (w : WinCheck vp prims) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfRealPrG ds (msgPrf vp prims)
        (bPrfMsgWLG ds optRand pkSeedDist w (wrapFam ds w' e g F'))) := by
  unfold prfRealPrG prfRealExperimentG bPrfMsgWLG lazyRunG msgOpenWG
  refine isLin_liftR_bind ds _ _ fun k ↦ ?_
  simp only [runGO_bind, runGO_embed, runGO_runGO, runGO_wrapFam, runGO_pure, runG_bind,
    runG_embedO, runG_runGO, runG_pure, bind_assoc, bind_map_left, map_bind, map_pure]
  refine isLin_liftR_bind ds _ _ fun y ↦ ?_
  refine isLin_liftR_bind ds _ _ fun y' ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity**, ideal world of the `PRF_msg` game, `bPrfMsgWLG`. -/
theorem isLin_bPrfMsgWLG_ideal (w : WinCheck vp prims) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prfIdealPrG ds (bPrfMsgWLG ds optRand pkSeedDist w (wrapFam ds w' e g F'))) := by
  unfold prfIdealPrG prfIdealExperimentG bPrfMsgWLG lazyRunG msgOpenWG
  simp only [runGO_bind, runGO_embed, runGO_runGO, runGO_wrapFam, runGO_pure, runG_bind,
    runG_embedO, runG_runGO, runG_pure, bind_assoc, bind_map_left, map_bind, map_pure]
  refine isLin_liftR_bind ds _ _ fun y ↦ ?_
  refine isLin_liftR_bind ds _ _ fun y' ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity** of the wrapper ITSR advantage of `bItsrLG`. -/
theorem isLin_bItsrLG :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      ITSRAdvantageG ds (bItsrLG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold ITSRAdvantageG ITSRExperimentG bItsrLG lazyRunG itsrOpenG
  dsimp only
  simp only [runGO_bind, runGO_embed, runGO_runGO, runGO_wrapFam, runGO_pure, runG_bind,
    runG_embedO, runG_runGO, runG_pure, bind_assoc, bind_map_left, map_bind, map_pure]
  refine isLin_liftR_bind ds _ _ fun y ↦ ?_
  refine isLin_liftR_bind ds _ _ fun y' ↦ ?_
  exact isLin_run_pure ds _ _ _ _

end Linearity

/-! ## Values on classical forgers -/

theorem prfRealPrG_bPrfMsgLG_embed (A : Forger vp prims optRand pkSeedDist) :
    prfRealPrG ds (msgPrf vp prims)
        (bPrfMsgLG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      msgRealPr (Lazy.bPrfMsgL A) := by
  rw [bPrfMsgLG_embed, prfRealPrG_embed]; rfl

theorem prfIdealPrG_bPrfMsgLG_embed (A : Forger vp prims optRand pkSeedDist) :
    prfIdealPrG ds (bPrfMsgLG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      msgIdealPr (Lazy.bPrfMsgL A) := by
  rw [bPrfMsgLG_embed, prfIdealPrG_embed]; rfl

theorem prfRealPrG_bPrfMsgWLG_embed (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prfRealPrG ds (msgPrf vp prims)
        (bPrfMsgWLG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk))) =
      msgRealPr (Lazy.bPrfMsgWL w A) := by
  rw [bPrfMsgWLG_embed, prfRealPrG_embed]; rfl

theorem prfIdealPrG_bPrfMsgWLG_embed (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prfIdealPrG ds (bPrfMsgWLG ds optRand pkSeedDist w (fun pk ↦ embed ds (A.main pk))) =
      msgIdealPr (Lazy.bPrfMsgWL w A) := by
  rw [bPrfMsgWLG_embed, prfIdealPrG_embed]; rfl

theorem ITSRAdvantageG_bItsrLG_embed (A : Forger vp prims optRand pkSeedDist) :
    ITSRAdvantageG ds (bItsrLG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      KeyedHash.ITSRAdvantage (Lazy.bItsrL A) := by
  rw [bItsrLG_embed, ITSRAdvantageG_ofClassical]

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms bPrfMsgLG_embed
#print axioms bPrfMsgWLG_embed
#print axioms bItsrLG_embed
#print axioms isLin_bPrfMsgLG_real
#print axioms isLin_bPrfMsgLG_ideal
#print axioms isLin_bPrfMsgWLG_real
#print axioms isLin_bPrfMsgWLG_ideal
#print axioms isLin_bItsrLG
#print axioms prfRealPrG_bPrfMsgLG_embed
#print axioms prfIdealPrG_bPrfMsgLG_embed
#print axioms prfRealPrG_bPrfMsgWLG_embed
#print axioms prfIdealPrG_bPrfMsgWLG_embed
#print axioms ITSRAdvantageG_bItsrLG_embed
end Axioms
