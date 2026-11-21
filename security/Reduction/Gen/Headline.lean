import Reduction.Gen.AdvPrf
import Reduction.Gen.AdvLazy
import Reduction.Gen.AdvOpenPre
import Reduction.Gen.AdvTcr
import Reduction.Gen.AdvWots
import Reduction.Gen.Wrappers
import Reduction.LinearBytes

/-!
# The reduction for forgers over a general sampling spec: linear form (typed and wrapped)

`linearIdealSideG`, `linearRealSideG`, `boundFinalTightG`: the two sides of the linear bound and
the absolute-value bound, in the wrapper games, as functions of general-spec adversaries.
`linIdeal{Euf,Suf}G`, `linReal{Euf,Suf}G`: the sides at the reduction adversaries around a forger
family.

`lin_transferG`: the generic step.  If `X` is an `IsLin` functional of an (outer) forger family
and the classical linear inequality `X + ideal ≤ real` holds for all classical outer families
(behind a classical forger-to-forger wrapper `w', e, g`), then it holds for all general-spec outer
families.  Proof: `derandG`; every term is `IsLin` (packages P1–P4) and reduces to the classical
term on `ds`-free families (naturality + coincidence of the wrapper games).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-! ## The two sides and the bound, in the wrapper games -/

/-- Left ("ideal") side of the linear bound, wrapper games. -/
noncomputable def linearIdealSideG
    (B₁ : PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : PRFAdversaryG ds (prims.Y × List Byte) prims.Y)
    (D : DsprFVAdversaryG ds (forsDsprProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_AdversaryG ds (wotsUdProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  prfIdealPrG ds B₁ + prfIdealPrG ds B₂ + dsprSPProbabilityG ds D +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_IdealSuccessG ds B₆

/-- Right ("real") side of the linear bound, wrapper games. -/
noncomputable def linearRealSideG
    (B₁ : PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : PRFAdversaryG ds (prims.Y × List Byte) prims.Y)
    (B₃ : ITSRAdversaryG ds (itsrProblem vp prims))
    (D : DsprFVAdversaryG ds (forsDsprProblem vp prims pkSeedDist))
    (T : TcrFVAdversaryG ds (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_AdversaryG ds (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_AdversaryG ds (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_AdversaryG ds (wotsTcrProblemT vp prims pkSeedDist)) : ℝ≥0∞ :=
  prfRealPrG ds (skPrfC vp prims) B₁ + prfRealPrG ds (msgPrf vp prims) B₂ +
    ITSRAdvantageG ds B₃ +
    (dsprSuccessG ds D + 3 * tcrFVAdvantageG ds T) +
    (SM_DT_TCR_AdvantageG ds C₁ + SM_DT_TCR_AdvantageG ds C₂ + SM_DT_TCR_AdvantageG ds C₃ +
      SM_DT_TCR_AdvantageG ds C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_RealSuccessG ds B₆ +
    SM_DT_PRE_AdvantageG ds B₇ +
    SM_DT_TCR_AdvantageG ds B₈

/-- The absolute-value bound (`boundFinalTight`), wrapper games: twelve advantages. -/
noncomputable def boundFinalTightG
    (B₁ : PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : PRFAdversaryG ds (prims.Y × List Byte) prims.Y)
    (B₃ : ITSRAdversaryG ds (itsrProblem vp prims))
    (D : DsprFVAdversaryG ds (forsDsprProblem vp prims pkSeedDist))
    (T : TcrFVAdversaryG ds (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_AdversaryG ds (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_AdversaryG ds (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_AdversaryG ds (wotsTcrProblemT vp prims pkSeedDist)) : ℝ≥0∞ :=
  prfAdvantageG ds (skPrfC vp prims) B₁ + prfAdvantageG ds (msgPrf vp prims) B₂ +
    ITSRAdvantageG ds B₃ +
    (dsprAdvantageG ds D + 3 * tcrFVAdvantageG ds T) +
    (SM_DT_TCR_AdvantageG ds C₁ + SM_DT_TCR_AdvantageG ds C₂ + SM_DT_TCR_AdvantageG ds C₃ +
      SM_DT_TCR_AdvantageG ds C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_AdvantageG ds B₆ +
    SM_DT_PRE_AdvantageG ds B₇ +
    SM_DT_TCR_AdvantageG ds B₈

/-! ## From the linear form to the absolute-value form -/

private theorem le_add_absDiff (r i : ℝ≥0∞) : r ≤ i + ENNReal.absDiff r i := by
  unfold ENNReal.absDiff
  calc r ≤ i + (r - i) := le_add_tsub
    _ ≤ i + ((r - i) + (i - r)) := by gcongr; exact le_self_add

private theorem of_linear_arithG
    {adv r1 i1 a1 r2 i2 a2 c Ds S dv T X n R I aU p t : ℝ≥0∞}
    (h1 : r1 ≤ i1 + a1) (h2 : r2 ≤ i2 + a2) (h3 : Ds ≤ S + dv) (h4 : R ≤ I + aU)
    (hfin : i1 + i2 + S + n * I ≠ ⊤)
    (h : adv + (i1 + i2 + S + n * I) ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t) :
    adv ≤ a1 + a2 + c + (dv + 3 * T) + X + n * aU + p + t := by
  have h' : adv + (i1 + i2 + S + n * I) ≤
      (a1 + a2 + c + (dv + 3 * T) + X + n * aU + p + t) + (i1 + i2 + S + n * I) :=
    calc adv + (i1 + i2 + S + n * I)
        ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t := h
      _ ≤ (i1 + a1) + (i2 + a2) + c + ((S + dv) + 3 * T) + X + n * (I + aU) + p + t := by
          gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 h'

theorem linearIdealSideG_ne_top
    (B₁ : PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : PRFAdversaryG ds (prims.Y × List Byte) prims.Y)
    (D : DsprFVAdversaryG ds (forsDsprProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_AdversaryG ds (wotsUdProblem vp prims pkSeedDist)) :
    linearIdealSideG ds pkSeedDist B₁ B₂ D B₆ ≠ ⊤ := by
  have h1 := (prfIdealPrG_le_one ds B₁).trans_lt ENNReal.one_lt_top
  have h2 := (prfIdealPrG_le_one ds B₂).trans_lt ENNReal.one_lt_top
  have h3 := (dsprSPProbabilityG_le_one ds D).trans_lt ENNReal.one_lt_top
  have h4 := (SM_DT_UD_IdealSuccessG_le_one ds B₆).trans_lt ENNReal.one_lt_top
  unfold linearIdealSideG
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨h1.ne, h2.ne⟩, h3.ne⟩,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) h4.ne⟩

/-- **The absolute-value bound follows from the linear bound** (wrapper games; any adversaries,
any left-hand quantity). -/
theorem boundFinalTightG_of_linear {adv : ℝ≥0∞}
    (B₁ : PRFAdversaryG ds (prims.PkSeed × SkAdrs vp) prims.Y)
    (B₂ : PRFAdversaryG ds (prims.Y × List Byte) prims.Y)
    (B₃ : ITSRAdversaryG ds (itsrProblem vp prims))
    (D : DsprFVAdversaryG ds (forsDsprProblem vp prims pkSeedDist))
    (T : TcrFVAdversaryG ds (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_AdversaryG ds (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_AdversaryG ds (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_AdversaryG ds (wotsTcrProblemT vp prims pkSeedDist))
    (h : adv + linearIdealSideG ds pkSeedDist B₁ B₂ D B₆ ≤
      linearRealSideG ds pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈) :
    adv ≤ boundFinalTightG ds pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈ := by
  have hfin := linearIdealSideG_ne_top ds pkSeedDist B₁ B₂ D B₆
  unfold linearIdealSideG at h hfin
  unfold linearRealSideG at h
  unfold boundFinalTightG
  exact of_linear_arithG (le_add_absDiff _ _) (le_add_absDiff _ _) le_add_tsub
    (le_add_absDiff _ _) hfin h

/-! ## The sides at the reduction adversaries -/

/-- The classical forger behind a classical forger-to-forger wrapper. -/
def clsFam {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
    (w' : QueryImpl (unifSpec + X')
      (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
    (e : PublicKeyCore prims.core → PK')
    (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core)
    (F₀ : PK' → OracleComp (unifSpec + X') α') : Forger vp prims optRand pkSeedDist :=
  ⟨fun pk ↦ g <$> simulateQ w' (F₀ (e pk))⟩

/-- Ideal side at the EUF reduction adversaries around the forger family `F`. -/
noncomputable def linIdealEufG (F : GFam ds vp prims) : ℝ≥0∞ :=
  linearIdealSideG ds pkSeedDist (bPrfCG ds optRand pkSeedDist F)
    (bPrfMsgLG ds optRand pkSeedDist F) (toDsprG ds optRand pkSeedDist F)
    (rUdG ds optRand pkSeedDist F)

/-- Real side at the EUF reduction adversaries around the forger family `F`. -/
noncomputable def linRealEufG (F : GFam ds vp prims) : ℝ≥0∞ :=
  linearRealSideG ds pkSeedDist (bPrfCG ds optRand pkSeedDist F)
    (bPrfMsgLG ds optRand pkSeedDist F) (bItsrLG ds optRand pkSeedDist F)
    (toDsprG ds optRand pkSeedDist F) (toTcrG ds optRand pkSeedDist F)
    (bTcrArMG ds optRand pkSeedDist 1 F) (bTcrArMG ds optRand pkSeedDist 2 F)
    (bTcrArMG ds optRand pkSeedDist vp.params.len F) (bTcrArMG ds optRand pkSeedDist vp.params.k F)
    (rUdG ds optRand pkSeedDist F) (rPreG ds optRand pkSeedDist F)
    (rTcrTG ds optRand pkSeedDist F)

/-- Ideal side at the SUF reduction adversaries around the forger family `F`. -/
noncomputable def linIdealSufG (F : GFam ds vp prims) : ℝ≥0∞ :=
  linearIdealSideG ds pkSeedDist (bPrfWCG ds optRand pkSeedDist sufCheck F)
    (bPrfMsgWLG ds optRand pkSeedDist sufCheck F) (toDsprG ds optRand pkSeedDist F)
    (rUdG ds optRand pkSeedDist F)

/-- Real side at the SUF reduction adversaries around the forger family `F`. -/
noncomputable def linRealSufG (F : GFam ds vp prims) : ℝ≥0∞ :=
  linearRealSideG ds pkSeedDist (bPrfWCG ds optRand pkSeedDist sufCheck F)
    (bPrfMsgWLG ds optRand pkSeedDist sufCheck F) (bItsrLG ds optRand pkSeedDist F)
    (toDsprG ds optRand pkSeedDist F) (toTcrG ds optRand pkSeedDist F)
    (bTcrArMG ds optRand pkSeedDist 1 F) (bTcrArMG ds optRand pkSeedDist 2 F)
    (bTcrArMG ds optRand pkSeedDist vp.params.len F) (bTcrArMG ds optRand pkSeedDist vp.params.k F)
    (rUdG ds optRand pkSeedDist F) (rPreG ds optRand pkSeedDist F)
    (rTcrTG ds optRand pkSeedDist F)

/-- The absolute-value bound at the EUF reduction adversaries around `F`
(general-spec `betaEufFinalMemo`). -/
noncomputable def betaEufG (F : GFam ds vp prims) : ℝ≥0∞ :=
  boundFinalTightG ds pkSeedDist (bPrfCG ds optRand pkSeedDist F)
    (bPrfMsgLG ds optRand pkSeedDist F) (bItsrLG ds optRand pkSeedDist F)
    (toDsprG ds optRand pkSeedDist F) (toTcrG ds optRand pkSeedDist F)
    (bTcrArMG ds optRand pkSeedDist 1 F) (bTcrArMG ds optRand pkSeedDist 2 F)
    (bTcrArMG ds optRand pkSeedDist vp.params.len F) (bTcrArMG ds optRand pkSeedDist vp.params.k F)
    (rUdG ds optRand pkSeedDist F) (rPreG ds optRand pkSeedDist F)
    (rTcrTG ds optRand pkSeedDist F)

/-- The absolute-value bound at the SUF reduction adversaries around `F`
(general-spec `betaSufFinalMemo`). -/
noncomputable def betaSufG (F : GFam ds vp prims) : ℝ≥0∞ :=
  boundFinalTightG ds pkSeedDist (bPrfWCG ds optRand pkSeedDist sufCheck F)
    (bPrfMsgWLG ds optRand pkSeedDist sufCheck F) (bItsrLG ds optRand pkSeedDist F)
    (toDsprG ds optRand pkSeedDist F) (toTcrG ds optRand pkSeedDist F)
    (bTcrArMG ds optRand pkSeedDist 1 F) (bTcrArMG ds optRand pkSeedDist 2 F)
    (bTcrArMG ds optRand pkSeedDist vp.params.len F) (bTcrArMG ds optRand pkSeedDist vp.params.k F)
    (rUdG ds optRand pkSeedDist F) (rPreG ds optRand pkSeedDist F)
    (rTcrTG ds optRand pkSeedDist F)

variable {optRand pkSeedDist}

/-! ## On classical forgers the sides are the classical sides -/

theorem linIdealEufG_embed (A : Forger vp prims optRand pkSeedDist) :
    linIdealEufG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = linIdealEuf A := by
  unfold linIdealEufG linearIdealSideG linIdealEuf linearIdealSide
  rw [prfIdealPrG_bPrfCG_embed, prfIdealPrG_bPrfMsgLG_embed, dsprSPProbabilityG_toDsprG_embed,
    udIdealG_rUdG_embed]

theorem linRealEufG_embed (A : Forger vp prims optRand pkSeedDist) :
    linRealEufG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = linRealEuf A := by
  unfold linRealEufG linearRealSideG linRealEuf linearRealSide
  rw [prfRealPrG_bPrfCG_embed, prfRealPrG_bPrfMsgLG_embed, ITSRAdvantageG_bItsrLG_embed,
    dsprSuccessG_toDsprG_embed, tcrFVAdvantageG_toTcrG_embed, udRealG_rUdG_embed,
    preAdvG_rPreG_embed, tcrAdvG_rTcrTG_embed]
  simp only [bTcrArMG_embed, SM_DT_TCR_AdvantageG_ofClassical]

theorem linIdealSufG_embed (A : Forger vp prims optRand pkSeedDist) :
    linIdealSufG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = linIdealSuf A := by
  unfold linIdealSufG linearIdealSideG linIdealSuf linearIdealSide
  rw [prfIdealPrG_bPrfWCG_embed, prfIdealPrG_bPrfMsgWLG_embed, dsprSPProbabilityG_toDsprG_embed,
    udIdealG_rUdG_embed]

theorem linRealSufG_embed (A : Forger vp prims optRand pkSeedDist) :
    linRealSufG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = linRealSuf A := by
  unfold linRealSufG linearRealSideG linRealSuf linearRealSide
  rw [prfRealPrG_bPrfWCG_embed, prfRealPrG_bPrfMsgWLG_embed, ITSRAdvantageG_bItsrLG_embed,
    dsprSuccessG_toDsprG_embed, tcrFVAdvantageG_toTcrG_embed, udRealG_rUdG_embed,
    preAdvG_rPreG_embed, tcrAdvG_rTcrTG_embed]
  simp only [bTcrArMG_embed, SM_DT_TCR_AdvantageG_ofClassical]

/-! ## Linearity of the sides and the generic step -/

section transfer

variable {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
  (w' : QueryImpl (unifSpec + X')
    (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
  (e : PublicKeyCore prims.core → PK')
  (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core)

theorem isLin_linIdealEufG :
    ∃ b : ℝ≥0∞, b ≠ ⊤ ∧ IsLin ds (wOf ds) b (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      linIdealEufG ds optRand pkSeedDist (wrapFam ds w' e g F')) := by
  have h1 := isLin_bPrfCG_ideal (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h2 := isLin_bPrfMsgLG_ideal (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h3 := isLin_toDsprG_spprob (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h4 := isLin_rUdG_ideal (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  refine ⟨1 + 1 + 1 + ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1, ?_,
    IsLin.add ds (IsLin.add ds (IsLin.add ds h1 h2) h3) (IsLin.const_mul ds _ h4)⟩
  simp [ENNReal.natCast_ne_top]

theorem isLin_linRealEufG :
    ∃ b : ℝ≥0∞, b ≠ ⊤ ∧ IsLin ds (wOf ds) b (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      linRealEufG ds optRand pkSeedDist (wrapFam ds w' e g F')) := by
  have h1 := isLin_bPrfCG_real (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h2 := isLin_bPrfMsgLG_real (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h3 := isLin_bItsrLG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h4 := isLin_toDsprG_success (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h5 := isLin_toTcrG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have c1 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds 1 w' e g
  have c2 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds 2 w' e g
  have c3 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds vp.params.len w' e g
  have c4 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds vp.params.k w' e g
  have h6 := isLin_rUdG_real (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h7 := isLin_rPreG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h8 := isLin_rTcrTG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  refine ⟨1 + 1 + 1 + (1 + 3 * 1) + (1 + 1 + 1 + 1) + ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1 + 1 + 1,
    ?_, IsLin.add ds (IsLin.add ds (IsLin.add ds (IsLin.add ds (IsLin.add ds
      (IsLin.add ds (IsLin.add ds h1 h2) h3) (IsLin.add ds h4 (IsLin.const_mul ds 3 h5)))
      (IsLin.add ds (IsLin.add ds (IsLin.add ds c1 c2) c3) c4))
      (IsLin.const_mul ds _ h6)) h7) h8⟩
  simp [ENNReal.natCast_ne_top]

/-- **Generic step (Euf reduction adversaries).**  A classical linear inequality behind a
classical forger-to-forger wrapper, for an `IsLin` left-hand functional `X`, holds for all
general-spec forger families. -/
theorem lin_transfer_eufG
    (X : (PK' → OracleComp ((ds + unifSpec) + X') α') → ℝ≥0∞) (hX : IsLin ds (wOf ds) 1 X)
    (h : ∀ F₀ : PK' → OracleComp (unifSpec + X') α',
      X (fun pk ↦ embed ds (F₀ pk)) + linIdealEuf (clsFam optRand pkSeedDist w' e g F₀) ≤
        linRealEuf (clsFam optRand pkSeedDist w' e g F₀)) :
    ∀ F' : PK' → OracleComp ((ds + unifSpec) + X') α',
      X F' + linIdealEufG ds optRand pkSeedDist (wrapFam ds w' e g F') ≤
        linRealEufG ds optRand pkSeedDist (wrapFam ds w' e g F') := by
  obtain ⟨bI, hbI, hI⟩ := isLin_linIdealEufG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  obtain ⟨bR, hbR, hR⟩ := isLin_linRealEufG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  refine derandG ds (bN := 1 + bI) (bP := bR) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hbI⟩)
    hbR (IsLin.add ds hX hI) hR ?_
  intro F₀
  have e1 := linIdealEufG_embed ds (clsFam optRand pkSeedDist w' e g F₀)
  have e2 := linRealEufG_embed ds (clsFam optRand pkSeedDist w' e g F₀)
  simp only [wrapFam_embed]
  change X _ + linIdealEufG ds optRand pkSeedDist
      (fun pk ↦ embed ds ((clsFam optRand pkSeedDist w' e g F₀).main pk)) ≤
    linRealEufG ds optRand pkSeedDist
      (fun pk ↦ embed ds ((clsFam optRand pkSeedDist w' e g F₀).main pk))
  rw [e1, e2]
  exact h F₀

theorem isLin_linIdealSufG :
    ∃ b : ℝ≥0∞, b ≠ ⊤ ∧ IsLin ds (wOf ds) b (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      linIdealSufG ds optRand pkSeedDist (wrapFam ds w' e g F')) := by
  have h1 := isLin_bPrfWCG_ideal (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g sufCheck
  have h2 := isLin_bPrfMsgWLG_ideal (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g sufCheck
  have h3 := isLin_toDsprG_spprob (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h4 := isLin_rUdG_ideal (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  refine ⟨1 + 1 + 1 + ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1, ?_,
    IsLin.add ds (IsLin.add ds (IsLin.add ds h1 h2) h3) (IsLin.const_mul ds _ h4)⟩
  simp [ENNReal.natCast_ne_top]

theorem isLin_linRealSufG :
    ∃ b : ℝ≥0∞, b ≠ ⊤ ∧ IsLin ds (wOf ds) b (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      linRealSufG ds optRand pkSeedDist (wrapFam ds w' e g F')) := by
  have h1 := isLin_bPrfWCG_real (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g sufCheck
  have h2 := isLin_bPrfMsgWLG_real (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g sufCheck
  have h3 := isLin_bItsrLG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h4 := isLin_toDsprG_success (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h5 := isLin_toTcrG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have c1 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds 1 w' e g
  have c2 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds 2 w' e g
  have c3 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds vp.params.len w' e g
  have c4 := isLin_bTcrArMG (optRand := optRand) (pkSeedDist := pkSeedDist) ds vp.params.k w' e g
  have h6 := isLin_rUdG_real (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h7 := isLin_rPreG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  have h8 := isLin_rTcrTG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  refine ⟨1 + 1 + 1 + (1 + 3 * 1) + (1 + 1 + 1 + 1) + ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * 1 + 1 + 1,
    ?_, IsLin.add ds (IsLin.add ds (IsLin.add ds (IsLin.add ds (IsLin.add ds
      (IsLin.add ds (IsLin.add ds h1 h2) h3) (IsLin.add ds h4 (IsLin.const_mul ds 3 h5)))
      (IsLin.add ds (IsLin.add ds (IsLin.add ds c1 c2) c3) c4))
      (IsLin.const_mul ds _ h6)) h7) h8⟩
  simp [ENNReal.natCast_ne_top]

/-- **Generic step (Suf reduction adversaries).**  A classical linear inequality behind a
classical forger-to-forger wrapper, for an `IsLin` left-hand functional `X`, holds for all
general-spec forger families. -/
theorem lin_transfer_sufG
    (X : (PK' → OracleComp ((ds + unifSpec) + X') α') → ℝ≥0∞) (hX : IsLin ds (wOf ds) 1 X)
    (h : ∀ F₀ : PK' → OracleComp (unifSpec + X') α',
      X (fun pk ↦ embed ds (F₀ pk)) + linIdealSuf (clsFam optRand pkSeedDist w' e g F₀) ≤
        linRealSuf (clsFam optRand pkSeedDist w' e g F₀)) :
    ∀ F' : PK' → OracleComp ((ds + unifSpec) + X') α',
      X F' + linIdealSufG ds optRand pkSeedDist (wrapFam ds w' e g F') ≤
        linRealSufG ds optRand pkSeedDist (wrapFam ds w' e g F') := by
  obtain ⟨bI, hbI, hI⟩ := isLin_linIdealSufG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  obtain ⟨bR, hbR, hR⟩ := isLin_linRealSufG (optRand := optRand) (pkSeedDist := pkSeedDist) ds w' e g
  refine derandG ds (bN := 1 + bI) (bP := bR) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hbI⟩)
    hbR (IsLin.add ds hX hI) hR ?_
  intro F₀
  have e1 := linIdealSufG_embed ds (clsFam optRand pkSeedDist w' e g F₀)
  have e2 := linRealSufG_embed ds (clsFam optRand pkSeedDist w' e g F₀)
  simp only [wrapFam_embed]
  change X _ + linIdealSufG ds optRand pkSeedDist
      (fun pk ↦ embed ds ((clsFam optRand pkSeedDist w' e g F₀).main pk)) ≤
    linRealSufG ds optRand pkSeedDist
      (fun pk ↦ embed ds ((clsFam optRand pkSeedDist w' e g F₀).main pk))
  rw [e1, e2]
  exact h F₀

end transfer

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms boundFinalTightG_of_linear
#print axioms lin_transfer_eufG
#print axioms lin_transfer_sufG
end Axioms
