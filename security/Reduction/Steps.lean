import Reduction.WotsGame

/-!
# Step statements

Each `Step…` is a self-contained `Prop`: one inequality between success probabilities of explicit
experiments, parameterised by the forger `A` and by the reduction adversary (or adversaries) it
mentions.  A work package owns the *definition* of its reduction adversary and the *proof* of the
step at that adversary; the statements in this file do not change.

`Reduction.Main.final_of_steps` composes the nine steps arithmetically.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

/-- Probability that a Boolean experiment returns `true`. -/
noncomputable def prTrue (g : ProbComp Bool) : ℝ≥0∞ := 𝒟[g] {true}

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## Adversary types of the eight named games -/

/-- Distinguisher against `PRF(·, SK.seed, ·)`. -/
abbrev SkPrfAdv (prims : Primitives vp.params) : Type :=
  PRFScheme.PRFAdversary (prims.PkSeed × Adrs) prims.Y

/-- Distinguisher against `PRF_msg(SK.prf, ·, ·)`. -/
abbrev MsgPrfAdv (prims : Primitives vp.params) : Type :=
  PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y

/-! ## Steps -/

/-- **Step 1 (PRF hop).** `Pr[G0] ≤ Pr[G1] + Adv^PRF_{PRF}(B)`. -/
def StepPRF (A : Forger vp prims optRand pkSeedDist) (B : SkPrfAdv prims) : Prop :=
  prTrue (g0 A) ≤ prTrue (g1 A) + (skPrf vp prims).prfAdvantage B

/-- **Step 2 (PRF_msg hop).** `Pr[G1] ≤ Pr[G2] + Adv^PRF_{PRF_msg}(B)`. -/
def StepPRFmsg (A : Forger vp prims optRand pkSeedDist) (B : MsgPrfAdv prims) : Prop :=
  prTrue (g1 A) ≤ prTrue (g2 A) + (msgPrf vp prims).prfAdvantage B

/-- **Step 3 (case split).** `Pr[G2] ≤ Σ_c Pr[G2 ∧ class = c]`.  Purely a partition of the
success event by the total function `classify`; no adversary, no assumption. -/
def StepSplit (A : Forger vp prims optRand pkSeedDist) : Prop :=
  prTrue (g2 A) ≤ prTrue (g2Class A .itsr) + prTrue (g2Class A .openpre) +
    prTrue (g2Class A .tcr) + prTrue (g2Class A .wots)

/-- **Step 4 (ITSR branch).** -/
def StepITSR (A : Forger vp prims optRand pkSeedDist)
    (B : KeyedHash.ITSRAdversary (itsrProblem vp prims)) : Prop :=
  prTrue (g2Class A .itsr) ≤ KeyedHash.ITSRAdvantage B

/-- **Step 5 (FORS open-preimage branch).** -/
def StepOpenPRE (A : Forger vp prims optRand pkSeedDist)
    (B : TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist)) : Prop :=
  prTrue (g2Class A .openpre) ≤ TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage B

/-- **Step 6 (collision branch).** -/
def StepTCR (A : Forger vp prims optRand pkSeedDist)
    (B : TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist)) : Prop :=
  prTrue (g2Class A .tcr) ≤ TweakableHash.SM_DT_TCR_Advantage B

/-- **Step 7 (embedding into the WOTS game).** -/
def StepWotsEmbed (A : Forger vp prims optRand pkSeedDist) (W : WotsGame.Adversary prims) :
    Prop :=
  prTrue (g2Class A .wots) ≤ prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 W)

/-- **Step 8 (undetectability hybrid).**  `Pr[Hyb₀] ≤ Pr[Hyb_{w-2}] + (w-2)·Adv^{SM-UD}_F(U)`. -/
def StepWotsUD (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims)
    (U : TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist)) : Prop :=
  prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 W) ≤
    prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (vp.params.w - 2) W) +
      ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * TweakableHash.SM_DT_UD_Advantage U

/-- **Step 9 (last hybrid).**  `Pr[Hyb_{w-2}] ≤ Adv^{SM-PRE}_F(P) + Adv^{SM-TCR}_F(T)`. -/
def StepWotsFinal (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims)
    (P : TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (T : TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) : Prop :=
  prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (vp.params.w - 2) W) ≤
    TweakableHash.SM_DT_PRE_Advantage P + TweakableHash.SM_DT_TCR_Advantage T

/-! ## The bound -/

/-- The right-hand side of the phase-1 theorem `slhdsa_euf_cma` (eight advantages). -/
noncomputable def bound (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : SkPrfAdv prims) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (B₄ : TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist))
    (B₅ : TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (B₆ : TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  (skPrf vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage B₄ +
    TweakableHash.SM_DT_TCR_Advantage B₅ +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * TweakableHash.SM_DT_UD_Advantage B₆ +
    TweakableHash.SM_DT_PRE_Advantage B₇ +
    TweakableHash.SM_DT_TCR_Advantage B₈

end Reduction
