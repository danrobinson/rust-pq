import Reduction.Steps

/-!
# Composition: the conditional final theorem

`final_of_steps` is the arithmetic composition of the nine steps.  It is conditional only on the
step statements, each of which is a precise named `Prop` of `Reduction.Steps`.  Every step is
proved at its concrete reduction adversary; `Reduction.Final` (`slhdsa_euf_cma`) supplies them, so
the hypotheses disappear there.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

omit [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- The EUF-CMA advantage is the success probability of `G0`. -/
theorem unforgeableAdvantage_eq_prTrue_g0 (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A = prTrue (g0 A) := by
  simp [SignatureAlg.unforgeableAdvantage, prTrue, g0, ProbCompRuntime.probComp_evalDist]

/-- **Final theorem, conditional form.**  For every chosen-message forger `A` against
`internalAlg vp prims optRand pkSeedDist` and every choice of the nine reduction adversaries
satisfying the nine step statements,

`Adv^{EUF-CMA}(A) ≤ Adv^PRF(B₁) + Adv^PRF_msg(B₂) + Adv^ITSR(B₃) + Adv^{SM-OpenPRE}_F(B₄)
  + Adv^{SM-TCR}_{Thash}(B₅) + (w-2)·Adv^{SM-UD}_F(B₆) + Adv^{SM-PRE}_F(B₇) + Adv^{SM-TCR}_F(B₈)`. -/
theorem final_of_steps (A : Forger vp prims optRand pkSeedDist)
    (B₁ : SkPrfAdv prims) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (B₄ : TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist))
    (B₅ : TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (W : WotsGame.Adversary prims)
    (B₆ : TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist))
    (h₁ : StepPRF A B₁) (h₂ : StepPRFmsg A B₂) (h₃ : StepSplit A)
    (h₄ : StepITSR A B₃) (h₅ : StepOpenPRE A B₄) (h₆ : StepTCR A B₅)
    (h₇ : StepWotsEmbed A W) (h₈ : StepWotsUD pkSeedDist W B₆)
    (h₉ : StepWotsFinal pkSeedDist W B₇ B₈) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ := by
  rw [unforgeableAdvantage_eq_prTrue_g0]
  unfold StepPRF at h₁; unfold StepPRFmsg at h₂; unfold StepSplit at h₃
  unfold StepITSR at h₄; unfold StepOpenPRE at h₅; unfold StepTCR at h₆
  unfold StepWotsEmbed at h₇; unfold StepWotsUD at h₈; unfold StepWotsFinal at h₉
  unfold bound
  have hw := h₇.trans (h₈.trans (add_le_add_left h₉ _))
  calc prTrue (g0 A) ≤ prTrue (g1 A) + _ := h₁
    _ ≤ (prTrue (g2 A) + _) + _ := by gcongr
    _ ≤ ((prTrue (g2Class A .itsr) + prTrue (g2Class A .openpre) +
          prTrue (g2Class A .tcr) + prTrue (g2Class A .wots)) + _) + _ := by gcongr
    _ ≤ ((KeyedHash.ITSRAdvantage B₃ +
          TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage B₄ +
          TweakableHash.SM_DT_TCR_Advantage B₅ +
          (TweakableHash.SM_DT_PRE_Advantage B₇ + TweakableHash.SM_DT_TCR_Advantage B₈ +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * TweakableHash.SM_DT_UD_Advantage B₆)) +
          (msgPrf vp prims).prfAdvantage B₂) + (skPrf vp prims).prfAdvantage B₁ := by gcongr
    _ = _ := by ring

end Reduction
