import Reduction.Gen.Forger
import Reduction.Gen.GameFV
import Reduction.Lazy.OpenPreSparse

/-!
# The SM-DSPR and SM-TCR adversaries of the FORS-leaf term around a general-spec forger

Classically the two adversaries are `toDspr (Lazy.bOpenPreS A)` and `toTcr (Lazy.bOpenPreS A)`
(VCVio's `toDSPR` / `toTCR` applied to the sparse SM-DT-OpenPRE adversary).  Here they are defined
directly around a forger family `F : GFam ds vp prims`:

* selection phases `chooseOpenPreTcr`, `chooseOpenPreDspr`: the classical ones (they do not depend
  on the forger), embedded;
* `findOpenPreG`: the `find` phase of `Lazy.bOpenPreS`, an open program with the opening oracle;
  the forger is run by `runGO` against the handler `openPreHarness` of `runForgerLog`;
* guess/forge phases: the code of `toDSPR` / `toTCR` — one run of `find` against VCVio's opening
  simulation `findOracles targets` (now `runG`), then the classical translation of the output.

`toDsprG_embed`, `toTcrG_embed`: naturality.  `isLin_toDsprG_success`, `isLin_toDsprG_spprob`,
`isLin_toTcrG`: linearity behind arbitrary forger-to-forger wrappers.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets openPreTargets forsLeafKeys

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- The private state of both adversaries: the sparse table, the sampled targets, their images. -/
abbrev OpenPreSt (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y

/-- Selection phase of `toTcr (Lazy.bOpenPreS ·)` (it does not depend on the forger), with its
state type explicit. -/
noncomputable def chooseOpenPreTcr :
    OracleComp (unifSpec +
      (SM_DT_TCR_SourceFinalValidity.challengeSpec prims.AdrsKey prims.Y prims.Y +
        SourceFinalValidity.collectionSpec (forsTcrProblem vp prims pkSeedDist).thColl))
      (OpenPreSt vp prims) :=
  (toTcr (Lazy.bOpenPreS (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)))).choose

/-- Selection phase of `toDspr (Lazy.bOpenPreS ·)` (it does not depend on the forger), with its
state type explicit. -/
noncomputable def chooseOpenPreDspr :
    OracleComp (unifSpec +
      (SM_DT_DSPR_SourceFinalValidity.challengeSpec prims.AdrsKey prims.Y prims.Y +
        SourceFinalValidity.collectionSpec (forsDsprProblem vp prims pkSeedDist).thColl))
      (OpenPreSt vp prims) :=
  (toDspr (Lazy.bOpenPreS (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)))).choose

/-- The handler of `runForgerLog` inside the `find` phase of `bOpenPre`. -/
noncomputable def openPreHarness (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (unifSpec +
        SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
      SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y))).liftTarget
      (StateT (G2Log prims) (OracleComp (unifSpec +
        SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y))) +
    logSignOracle optRand (idealPk vp prims tbl pkSeed) lazyRandomizerLift
      (openSign (idealPk vp prims tbl pkSeed) tbl ys)

/-- The `find` phase of `Lazy.bOpenPreS` around a general-spec forger family (an open program
with the opening oracle). -/
noncomputable def findOpenPreG (F : GFam ds vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    OracleComp ((ds + unifSpec) + SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y)
      (ℕ × prims.Y) :=
  runGO ds (openPreHarness optRand tbl pkSeed ys) (F (idealPk vp prims tbl pkSeed)) [] >>=
    fun z ↦ pure (openPreAnswer (idealPk vp prims tbl pkSeed) ys z.2 z.1.1 z.1.2)

/-- Forge phase of `toTcrG`: `toTCR`'s forge phase around `findOpenPreG`. -/
noncomputable def forgeOpenPreG (F : GFam ds vp prims) (s : OpenPreSt vp prims)
    (pkSeed : prims.PkSeed) : OracleComp (gSpec ds) (ℕ × prims.Y) :=
  runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles s.2.1)
      (findOpenPreG ds optRand F s.1 pkSeed s.2.2) [] >>= fun z ↦ pure z.1

/-- Guess phase of `toDsprG`: `toDSPR`'s guess phase around `findOpenPreG`. -/
noncomputable def guessOpenPreG (F : GFam ds vp prims) (s : OpenPreSt vp prims)
    (pkSeed : prims.PkSeed) : OracleComp (gSpec ds) (ℕ × Bool) :=
  runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles s.2.1)
      (findOpenPreG ds optRand F s.1 pkSeed s.2.2) [] >>= fun z ↦
    pure (z.1.1, decide ((s.2.1[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2))

/-- **`toDspr (Lazy.bOpenPreS ·)` around a general-spec forger.** -/
noncomputable def toDsprG (F : GFam ds vp prims) :
    DsprFVAdversaryG ds (forsDsprProblem vp prims pkSeedDist) where
  State := OpenPreSt vp prims
  choose := embed ds (chooseOpenPreDspr optRand pkSeedDist)
  guess := guessOpenPreG ds optRand F

/-- **`toTcr (Lazy.bOpenPreS ·)` around a general-spec forger.** -/
noncomputable def toTcrG (F : GFam ds vp prims) :
    TcrFVAdversaryG ds (forsTcrProblem vp prims pkSeedDist) where
  State := OpenPreSt vp prims
  choose := embed ds (chooseOpenPreTcr optRand pkSeedDist)
  forge := forgeOpenPreG ds optRand F

variable {optRand pkSeedDist}

/-! ## Naturality -/

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- On a classical forger, `findOpenPreG` is the `find` phase of `Lazy.bOpenPreS`. -/
theorem findOpenPreG_embed (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    findOpenPreG ds optRand (fun pk ↦ embed ds (A.main pk)) tbl pkSeed ys =
      embed ds ((Lazy.bOpenPreS A).find tbl pkSeed ys) := by
  have h := embed_bind ds
    ((simulateQ (openPreHarness optRand tbl pkSeed ys) (A.main (idealPk vp prims tbl pkSeed))).run
      [])
    (fun z ↦ (pure (openPreAnswer (idealPk vp prims tbl pkSeed) ys z.2 z.1.1 z.1.2) :
      OracleComp (unifSpec + SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y) (ℕ × prims.Y)))
  simp only [embed_pure] at h
  simp only [findOpenPreG, runGO_embed]
  exact h.symm

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- A closed run of a `ds`-free `find` program followed by a pure translation. -/
theorem runG_find_embed {β : Type} (tg : List (prims.AdrsKey × prims.Y))
    (t : OracleComp (unifSpec + SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y) (ℕ × prims.Y))
    (f : (ℕ × prims.Y) × List ℕ → β) :
    (runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg) (embed ds t) [] >>= fun z ↦
        pure (f z)) =
      liftR ds ((simulateQ (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg) t).run [] >>=
        fun z ↦ pure (f z)) := by
  simp only [runG_embed, liftR_bind, liftR_pure]

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem forgeOpenPreG_embed (A : Forger vp prims optRand pkSeedDist) (s : OpenPreSt vp prims)
    (pkSeed : prims.PkSeed) :
    forgeOpenPreG ds optRand (fun pk ↦ embed ds (A.main pk)) s pkSeed =
      liftR ds ((toTcr (Lazy.bOpenPreS A)).forge s pkSeed) :=
  (congrArg (fun t ↦ runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles s.2.1) t [] >>=
      fun z ↦ pure z.1) (findOpenPreG_embed ds A s.1 pkSeed s.2.2)).trans
    (runG_find_embed ds s.2.1 _ fun z ↦ z.1)

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem guessOpenPreG_embed (A : Forger vp prims optRand pkSeedDist) (s : OpenPreSt vp prims)
    (pkSeed : prims.PkSeed) :
    guessOpenPreG ds optRand (fun pk ↦ embed ds (A.main pk)) s pkSeed =
      liftR ds ((toDspr (Lazy.bOpenPreS A)).guess s pkSeed) :=
  (congrArg (fun t ↦ runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles s.2.1) t [] >>=
      fun z : (ℕ × prims.Y) × List ℕ ↦ pure (z.1.1,
        decide ((s.2.1[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)))
    (findOpenPreG_embed ds A s.1 pkSeed s.2.2)).trans
    (runG_find_embed ds s.2.1 _ fun z ↦ (z.1.1,
      decide ((s.2.1[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)))

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `toDsprG` is `toDspr (Lazy.bOpenPreS A)`. -/
theorem toDsprG_embed (A : Forger vp prims optRand pkSeedDist) :
    toDsprG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      DsprFVAdversaryG.ofClassical ds (toDspr (Lazy.bOpenPreS A)) := by
  unfold toDsprG DsprFVAdversaryG.ofClassical
  congr 1
  funext s pkSeed
  exact guessOpenPreG_embed ds A s pkSeed

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **Naturality.** On a classical forger, `toTcrG` is `toTcr (Lazy.bOpenPreS A)`. -/
theorem toTcrG_embed (A : Forger vp prims optRand pkSeedDist) :
    toTcrG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      TcrFVAdversaryG.ofClassical ds (toTcr (Lazy.bOpenPreS A)) := by
  unfold toTcrG TcrFVAdversaryG.ofClassical
  congr 1
  funext s pkSeed
  exact forgeOpenPreG_embed ds A s pkSeed

/-! ## Linearity -/

section Linearity

variable {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
  (w' : QueryImpl (unifSpec + X')
    (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
  (e : PublicKeyCore prims.core → PK')
  (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core)

/-- **Linearity** of the wrapper TCR advantage of `toTcrG`. -/
theorem isLin_toTcrG :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      tcrFVAdvantageG ds (toTcrG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold tcrFVAdvantageG tcrFVExperimentG toTcrG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  simp only [runG_embed, forgeOpenPreG, findOpenPreG, runGO_wrapFam, runG_bind,
    runG_runGO, runG_pure, bind_assoc, bind_map_left, pure_bind]
  refine isLin_liftR_bind ds _ _ fun r ↦ ?_
  exact isLin_run_pure ds _ _ _ _

variable [Fintype prims.Y]

/-- Linearity of a run of `toDsprG` with any final predicate. -/
theorem isLin_toDsprG_run (win : prims.PkSeed →
      SM_DT_DSPR_SourceFinalValidity.State prims.AdrsKey prims.Y → ℕ × Bool → Bool) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      prG ds (dsprRunG ds win (toDsprG ds optRand pkSeedDist (wrapFam ds w' e g F')))) := by
  unfold dsprRunG toDsprG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  simp only [runG_embed, guessOpenPreG, findOpenPreG, runGO_wrapFam, runG_bind,
    runG_runGO, runG_pure, bind_assoc, bind_map_left, pure_bind]
  refine isLin_liftR_bind ds _ _ fun r ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity** of the DSPR success probability of `toDsprG`. -/
theorem isLin_toDsprG_success :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      dsprSuccessG ds (toDsprG ds optRand pkSeedDist (wrapFam ds w' e g F'))) :=
  isLin_toDsprG_run ds w' e g _

/-- **Linearity** of the `SPprob` baseline probability of `toDsprG`. -/
theorem isLin_toDsprG_spprob :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      dsprSPProbabilityG ds (toDsprG ds optRand pkSeedDist (wrapFam ds w' e g F'))) :=
  isLin_toDsprG_run ds w' e g _

end Linearity

/-! ## Values on classical forgers -/

theorem tcrFVAdvantageG_toTcrG_embed (A : Forger vp prims optRand pkSeedDist) :
    tcrFVAdvantageG ds (toTcrG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_TCR_SourceFinalValidity.advantage (toTcr (Lazy.bOpenPreS A)) := by
  rw [toTcrG_embed, tcrFVAdvantageG_ofClassical]

variable [Fintype prims.Y]

theorem dsprSuccessG_toDsprG_embed (A : Forger vp prims optRand pkSeedDist) :
    dsprSuccessG ds (toDsprG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_DSPR_SourceFinalValidity.Success (toDspr (Lazy.bOpenPreS A)) := by
  rw [toDsprG_embed, dsprSuccessG_ofClassical]

theorem dsprSPProbabilityG_toDsprG_embed (A : Forger vp prims optRand pkSeedDist) :
    dsprSPProbabilityG ds (toDsprG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (Lazy.bOpenPreS A)) := by
  rw [toDsprG_embed, dsprSPProbabilityG_ofClassical]

theorem dsprAdvantageG_toDsprG_embed (A : Forger vp prims optRand pkSeedDist) :
    dsprAdvantageG ds (toDsprG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (Lazy.bOpenPreS A)) := by
  rw [toDsprG_embed, dsprAdvantageG_ofClassical]

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms toDsprG_embed
#print axioms toTcrG_embed
#print axioms isLin_toDsprG_success
#print axioms isLin_toDsprG_spprob
#print axioms isLin_toTcrG
#print axioms dsprSuccessG_toDsprG_embed
#print axioms dsprSPProbabilityG_toDsprG_embed
#print axioms dsprAdvantageG_toDsprG_embed
#print axioms tcrFVAdvantageG_toTcrG_embed
end Axioms
