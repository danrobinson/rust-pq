import Reduction.VerifyArity

/-!
# The per-arity SM-TCR split, unconditional

`Reduction/TcrSplitFinal.lean` proves the split of the single SM-TCR term on the variable-arity
`Thash` into the four per-arity terms (`F`, `H`, `T_len`, `T_k`) conditionally on the named
hypothesis `VerifyAritySound vp prims`.  `Reduction/VerifyArity.lean` proves that hypothesis
(`verifyAritySound`).  Here the three conditional theorems are restated without it:

* `stepTCR_split'` — `Pr[G2 ∧ class = tcr] ≤ Σ_{n ∈ {1, 2, len, k}} Adv(bTcrAr n A)`;
* `slhdsa_euf_cma_tcr_split'` — the phase-1 bound (`slhdsa_euf_cma`) with `tcrSplitSum A`;
* `slhdsa_euf_cma_fors_tight_tcr_split'` — additionally with the tight FORS term;

and instantiated at SLH-DSA-SHA2-128s (no hypothesis except the forger).  The games, the
adversaries (`bTcrAr n A = TcrSplit.restrict … (bTcr A)`) and the bounds are exactly those of
`TcrSplitFinal.lean`; nothing new is defined.  These are phase-1-level statements (old PRF game
`skPrf`, eager-table adversaries, EUF-CMA); the current theorems with the split are
`slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_split` in `Reduction/HeadlineSplit.lean`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MeasureTheory

namespace Reduction

open TweakableHash

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **Step 6, split per arity (unconditional).**
`Pr[G2 ∧ class = tcr] ≤ Σ_{n ∈ {1, 2, len, k}} Adv^{SM-TCR}_{Thash|arity n}(bTcrAr n A)`. -/
theorem stepTCR_split' (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2Class A .tcr) ≤ ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities vp i) A) :=
  stepTCR_split hS verifyAritySound A

/-- **The phase-1 bound with the `Thash` SM-TCR term split per arity (unconditional).**

`Adv^{EUF-CMA}(A) ≤ Adv^{PRF}(bPrf A) + Adv^{PRF_msg}(bPrfMsg A) + Adv^{ITSR}(bItsr A)
   + Adv^{SM-OpenPRE}_F(bOpenPre A)
   + [Adv^{SM-TCR}_F(bTcrAr 1 A) + Adv^{SM-TCR}_H(bTcrAr 2 A)
      + Adv^{SM-TCR}_{T_len}(bTcrAr len A) + Adv^{SM-TCR}_{T_k}(bTcrAr k A)]
   + (w−2)·Adv^{SM-UD}_F(rUd (bWots A)) + Adv^{SM-PRE}_F(rPre (bWots A))
   + Adv^{SM-TCR}_F(rTcr (bWots A))`. -/
theorem slhdsa_euf_cma_tcr_split' (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf vp prims).prfAdvantage (bPrf A) + (msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) + tcrSplitSum A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  slhdsa_euf_cma_tcr_split hS verifyAritySound A

/-- **Both strengthenings, unconditional: tight FORS term and per-arity TCR terms.** -/
theorem slhdsa_euf_cma_fors_tight_tcr_split' [Fintype prims.Y] (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf vp prims).prfAdvantage (bPrf A) + (msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPre A)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPre A))) + tcrSplitSum A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  slhdsa_euf_cma_fors_tight_tcr_split hS verifyAritySound A

/-! ## SLH-DSA-SHA2-128s -/

/-- `VerifyAritySound` at SLH-DSA-SHA2-128s. -/
theorem verifyAritySound_128s : VerifyAritySound Link.vp Link.prims := verifyAritySound

/-- The split step at SLH-DSA-SHA2-128s. -/
theorem stepTCR_split_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    prTrue (g2Class A .tcr) ≤ ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities Link.vp i) A) :=
  stepTCR_split' structural_128s A

/-- The per-arity bound at SLH-DSA-SHA2-128s; no hypothesis except the forger. -/
theorem slhdsa_sha2_128s_euf_cma_tcr_split
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf Link.vp Link.prims).prfAdvantage (bPrf A) +
        (msgPrf Link.vp Link.prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) + tcrSplitSum A +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  slhdsa_euf_cma_tcr_split' structural_128s A

/-- The tight-FORS, per-arity bound at SLH-DSA-SHA2-128s; no hypothesis except the forger. -/
theorem slhdsa_sha2_128s_euf_cma_fors_tight_tcr_split
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf Link.vp Link.prims).prfAdvantage (bPrf A) +
        (msgPrf Link.vp Link.prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPre A)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPre A))) + tcrSplitSum A +
        ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  slhdsa_euf_cma_fors_tight_tcr_split' structural_128s A

/-- At SLH-DSA-SHA2-128s the four arities `1, 2, len = 35, k = 14` are pairwise distinct, so the
four terms of `tcrSplitSum` are four different games (not needed for the bounds above). -/
theorem arities_injective_128s : Function.Injective (arities Link.vp) := by
  decide

#print axioms stepTCR_split'
#print axioms slhdsa_euf_cma_tcr_split'
#print axioms slhdsa_euf_cma_fors_tight_tcr_split'
#print axioms verifyAritySound_128s
#print axioms stepTCR_split_128s
#print axioms slhdsa_sha2_128s_euf_cma_tcr_split
#print axioms slhdsa_sha2_128s_euf_cma_fors_tight_tcr_split
#print axioms arities_injective_128s

end Reduction
