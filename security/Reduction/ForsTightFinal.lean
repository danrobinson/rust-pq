import Reduction.Final
import Reduction.NonVacuity
import Reduction.Instance128s
import Reduction.ForsTight

/-!
# The phase-1 bound with the FORS-leaf term reduced to SM-DSPR + 3·SM-TCR on `F`

`Reduction.slhdsa_euf_cma` has the summand `Adv^{SM-DT-OpenPRE}_F(bOpenPre A)`.  The generic
theorem `ForsTight.openPRE_le_dspr_add_three_tcr` (for an arbitrary OpenPRE adversary) replaces
it by the paper's

`max 0 (Pr[SM-DSPR_F(toDspr B)] − Pr[SPprob_F(toDspr B)]) + 3 · Adv^{SM-TCR}_F(toTcr B)`.

Contents.

* `forsDsprProblem`, `forsTcrProblem`: the two games (VCVio's source-final-validity SM-DT-DSPR
  and SM-DT-TCR, stand-alone on `F`, cap `openPreTargets vp = 2^h · k · 2^a`).
* `toDspr B`, `toTcr B`: the explicit reductions (VCVio's `toDSPR`, `toTCR`) for an arbitrary
  OpenPRE adversary `B` of `forsOpenPreProblem`; resource lemmas `toTcr_choose_run`,
  `toDspr_choose_run`, `toTcr_targets`, `toDspr_targets`, `toTcr_forge`, `toDspr_guess`.
* `forsOpenPre_le` : the generic inequality at `forsOpenPreProblem`.
* `boundForsTight`, `bound_le_boundForsTight`, `forsTight_of_bound` (modular `∀ A` form),
  `slhdsa_euf_cma_fors_tight`, `slhdsa_sha2_128s_euf_cma_fors_tight`.
* Non-vacuity of the two new games: `Reduction/ForsTightNonVacuity.lean`.

The DSPR game needs `[Fintype prims.Y]` (its winning predicate decides whether a second preimage
exists); this is a class argument of the statements, supplied at 128s by
`instFintypeY128s` (`Y = Vector UInt8 16`).  No adversary uses it.
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

/-! ## The two games -/

variable (vp prims) in
/-- SM-DT-DSPR on `F` for the FORS leaves (HK22 Def. 5/7; EC `SMDTDSPR`): stand-alone, at most
`openPreTargets vp` targets, pairwise distinct target tweaks. -/
def forsDsprProblem (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_DSPR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey prims.Y prims.Y :=
  .standalone (fHash vp prims pkSeedDist) (openPreTargets vp)

variable (vp prims) in
/-- SM-DT-TCR on `F` for the FORS leaves (HK22 Def. 2/7; EC `SMDTTCR`): stand-alone, at most
`openPreTargets vp` targets, pairwise distinct target tweaks.  Only arity-one messages. -/
def forsTcrProblem (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_TCR_SourceFinalValidity.Problem Empty prims.PkSeed prims.AdrsKey prims.Y prims.Y :=
  .standalone (fHash vp prims pkSeedDist) (openPreTargets vp)

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
  [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y] in
theorem forsOpenPreProblem_toDSPR :
    (forsOpenPreProblem vp prims pkSeedDist).toDSPR = forsDsprProblem vp prims pkSeedDist := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
  [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y] in
theorem forsOpenPreProblem_toTCR :
    (forsOpenPreProblem vp prims pkSeedDist).toTCR = forsTcrProblem vp prims pkSeedDist := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
  [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y] in
theorem forsOpenPreProblem_uniform :
    (forsOpenPreProblem vp prims pkSeedDist).HasUniformInputs := rfl

/-! ## The two reductions -/

/-- OpenPRE adversaries of the FORS-leaf game. -/
abbrev ForsOpenPreAdv (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] (pkSeedDist : ProbComp prims.PkSeed) : Type 1 :=
  SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsOpenPreProblem vp prims pkSeedDist)

/-- The SM-DSPR adversary obtained from an arbitrary OpenPRE adversary `B` (VCVio's `toDSPR`).
Selection phase: run `B.pick` once, keep the first `openPreTargets vp` tweaks, sample one uniform
input per kept tweak and submit `(tweak, input)` as a target.  Guess phase: run `B.find` once,
answering opening query `j` with the `j`-th sampled input; on output `(j, m)` return
`(j, [m ≠ xⱼ ∨ j was opened])`. -/
noncomputable def toDspr (B : ForsOpenPreAdv vp prims pkSeedDist) :
    SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist) :=
  SM_DT_OpenPRE_SourceFinalValidity.toDSPR B

/-- The SM-TCR adversary obtained from an arbitrary OpenPRE adversary `B` (VCVio's `toTCR`).
Same selection phase as `toDspr B`; forge phase: run `B.find` once with the same opening
simulation and forward its output `(j, m)`. -/
noncomputable def toTcr (B : ForsOpenPreAdv vp prims pkSeedDist) :
    SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist) :=
  SM_DT_OpenPRE_SourceFinalValidity.toTCR B

section Resources

open SM_DT_OpenPRE_SourceFinalValidity

/-- **Selection phase of `toTcr B` inside its game.**  It is: `B.pick` (run once, in `B`'s own
commitment-phase oracles), then one uniform sample per retained tweak; the targets issued are
exactly these `(tweak, input)` pairs. -/
theorem toTcr_choose_run (B : ForsOpenPreAdv vp prims pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
        (toTcr B).choose).run .initial =
      (simulateQ (pickOracles (forsOpenPreProblem vp prims pkSeedDist) pk) B.pick).run .initial >>=
        fun w => ForsTight.sampleT ($ᵗ prims.Y) (w.1.2.take (openPreTargets vp)) >>= fun tg =>
          pure ((w.1.1, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
            ForsTight.recAll (openPreTargets vp) w.2 tg) :=
  ForsTight.red_choose_run B pk .initial

/-- **Selection phase of `toDspr B` inside its game**: literally that of `toTcr B`. -/
theorem toDspr_choose_run (B : ForsOpenPreAdv vp prims pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
        (toDspr B).choose).run .initial =
      (simulateQ (pickOracles (forsOpenPreProblem vp prims pkSeedDist) pk) B.pick).run .initial >>=
        fun w => ForsTight.sampleT ($ᵗ prims.Y) (w.1.2.take (openPreTargets vp)) >>= fun tg =>
          pure ((w.1.1, tg, ForsTight.images (fHash vp prims pkSeedDist) pk tg),
            ForsTight.recAll (openPreTargets vp) w.2 tg) :=
  ForsTight.red_choose_run B pk .initial

/-- **Target count of `toTcr B`.**  In every run, the targets are one per tweak of the retained
prefix of `B`'s commitment, in order; in particular at most `openPreTargets vp`, and never more
than `B` committed to. -/
theorem toTcr_targets (B : ForsOpenPreAdv vp prims pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ
        (SM_DT_TCR_SourceFinalValidity.oracles (forsTcrProblem vp prims pkSeedDist) pk)
        (toTcr B).choose).run .initial),
      ∃ w ∈ support ((simulateQ (pickOracles (forsOpenPreProblem vp prims pkSeedDist) pk)
          B.pick).run .initial),
        z.2.challenges.map Prod.fst = w.1.2.take (openPreTargets vp) ∧
          z.2.challenges.length ≤ openPreTargets vp ∧ z.2.challenges.length ≤ w.1.2.length := by
  intro z hz
  obtain ⟨w, hw, -, -, h3, h4⟩ := ForsTight.red_choose_targets B pk z hz
  refine ⟨w, hw, h3, h4, ?_⟩
  have := congrArg List.length h3
  rw [List.length_map, List.length_take] at this
  rw [this]
  exact Nat.min_le_right _ _

/-- **Target count of `toDspr B`**: as for `toTcr B`. -/
theorem toDspr_targets (B : ForsOpenPreAdv vp prims pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ
        (SM_DT_DSPR_SourceFinalValidity.oracles (forsDsprProblem vp prims pkSeedDist) pk)
        (toDspr B).choose).run .initial),
      ∃ w ∈ support ((simulateQ (pickOracles (forsOpenPreProblem vp prims pkSeedDist) pk)
          B.pick).run .initial),
        z.2.challenges.map Prod.fst = w.1.2.take (openPreTargets vp) ∧
          z.2.challenges.length ≤ openPreTargets vp ∧ z.2.challenges.length ≤ w.1.2.length :=
  toTcr_targets B pk

/-- **Second phase of `toTcr B`**: one run of `B.find`, opening query `j` answered by a list
lookup in the sampled targets; the output is forwarded. -/
theorem toTcr_forge (B : ForsOpenPreAdv vp prims pkSeedDist) (s : B.State)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pk : prims.PkSeed) :
    (toTcr B).forge (s, tg, ys) pk =
      (simulateQ (findOracles tg) (B.find s pk ys)).run [] >>= fun z => pure z.1 := rfl

/-- **Second phase of `toDspr B`**: one run of `B.find` with the same opening simulation, then a
constant-time comparison. -/
theorem toDspr_guess (B : ForsOpenPreAdv vp prims pkSeedDist) (s : B.State)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pk : prims.PkSeed) :
    (toDspr B).guess (s, tg, ys) pk =
      (simulateQ (findOracles tg) (B.find s pk ys)).run [] >>= fun z =>
        pure (z.1.1, decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)) := rfl

end Resources

/-! ## The generic inequality at the FORS-leaf problem -/

variable [Fintype prims.Y]

/-- **SM-DT-OpenPRE on `F` from SM-DSPR and SM-TCR on `F`, for every OpenPRE adversary.**

`Adv^{OpenPRE}_F(B) ≤ max 0 (Pr[DSPR(toDspr B)] − Pr[SPprob(toDspr B)]) + 3·Adv^{TCR}_F(toTcr B)`.

Unconditional (no interface or hypothesis), coefficients of HK22 / EasyCrypt
`OpenPRE_From_TCR_DSPR_THF`. -/
theorem forsOpenPre_le (B : ForsOpenPreAdv vp prims pkSeedDist) :
    SM_DT_OpenPRE_SourceFinalValidity.advantage B ≤
      SM_DT_DSPR_SourceFinalValidity.advantage (toDspr B) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr B) :=
  ForsTight.openPRE_le_dspr_add_three_tcr forsOpenPreProblem_uniform B

/-! ## The bound -/

/-- The right-hand side of the phase-1 theorem `slhdsa_euf_cma` with the OpenPRE summand
replaced by `DSPR + 3·TCR` on `F`.  Arguments as for `Reduction.bound`, with the 4th slot split in two. -/
noncomputable def boundForsTight (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : SkPrfAdv prims) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (T : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))
    (B₅ : SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  (skPrf vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.advantage D +
      3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    SM_DT_TCR_Advantage B₅ +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ +
    SM_DT_PRE_Advantage B₇ +
    SM_DT_TCR_Advantage B₈

/-- `bound` with an arbitrary OpenPRE adversary `B₄` in the 4th slot is at most `boundForsTight`
at `toDspr B₄`, `toTcr B₄`; all other slots unchanged. -/
theorem bound_le_boundForsTight (B₁ : SkPrfAdv prims) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (B₄ : ForsOpenPreAdv vp prims pkSeedDist)
    (B₅ : SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) :
    bound pkSeedDist B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ ≤
      boundForsTight pkSeedDist B₁ B₂ B₃ (toDspr B₄) (toTcr B₄) B₅ B₆ B₇ B₈ := by
  unfold bound boundForsTight
  have h := forsOpenPre_le B₄
  gcongr

/-- **Modular form.**  Any family of statements `Adv a ≤ bound … (b₄ a) …` (for instance the
phase-1 theorem, or package A's table-free variant with a different OpenPRE adversary in the 4th
slot) yields `Adv a ≤ boundForsTight … (toDspr (b₄ a)) (toTcr (b₄ a)) …`. -/
theorem forsTight_of_bound {α : Sort*} (Adv : α → ℝ≥0∞)
    (b₁ : α → SkPrfAdv prims) (b₂ : α → MsgPrfAdv prims)
    (b₃ : α → KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (b₄ : α → ForsOpenPreAdv vp prims pkSeedDist)
    (b₅ : α → SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist))
    (b₆ : α → SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (b₇ : α → SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (b₈ : α → SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist))
    (h : ∀ a, Adv a ≤ bound pkSeedDist (b₁ a) (b₂ a) (b₃ a) (b₄ a) (b₅ a) (b₆ a) (b₇ a) (b₈ a)) :
    ∀ a, Adv a ≤ boundForsTight pkSeedDist (b₁ a) (b₂ a) (b₃ a) (toDspr (b₄ a)) (toTcr (b₄ a))
      (b₅ a) (b₆ a) (b₇ a) (b₈ a) :=
  fun a => (h a).trans (bound_le_boundForsTight _ _ _ _ _ _ _ _)

/-- **Standard-model EUF-CMA security of SLH-DSA with the tight FORS term.**

`Adv^{EUF-CMA}(A) ≤ Adv^{PRF}(bPrf A) + Adv^{PRF_msg}(bPrfMsg A) + Adv^{ITSR}(bItsr A)
   + max 0 (Pr[SM-DSPR_F] − Pr[SPprob_F])(toDspr (bOpenPre A)) + 3·Adv^{SM-TCR}_F(toTcr (bOpenPre A))
   + Adv^{SM-TCR}_{Thash}(bTcr A) + (w−2)·Adv^{SM-UD}_F(rUd (bWots A))
   + Adv^{SM-PRE}_F(rPre (bWots A)) + Adv^{SM-TCR}_F(rTcr (bWots A))`.

Same left-hand side and hypotheses as `slhdsa_euf_cma` (plus the class `Fintype prims.Y` needed
to state the DSPR game). -/
theorem slhdsa_euf_cma_fors_tight (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundForsTight pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A)
        (toDspr (bOpenPre A)) (toTcr (bOpenPre A)) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) :=
  forsTight_of_bound (fun A : Forger vp prims optRand pkSeedDist =>
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A)
    bPrf bPrfMsg bItsr bOpenPre bTcr (fun A => rUd pkSeedDist (bWots A))
    (fun A => rPre pkSeedDist (bWots A)) (fun A => rTcr pkSeedDist (bWots A))
    (fun A => slhdsa_euf_cma hS A) A

/-! ## SLH-DSA-SHA2-128s -/

/-- `Y = Vector UInt8 16` is finite (needed only to state the DSPR game). -/
instance instFintypeY128s : Fintype Link.prims.Y := inferInstanceAs (Fintype (Vector UInt8 16))

/-- The tight-FORS bound at SLH-DSA-SHA2-128s; no hypothesis except the forger. -/
theorem slhdsa_sha2_128s_euf_cma_fors_tight
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundForsTight pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A)
        (toDspr (bOpenPre A)) (toTcr (bOpenPre A)) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) :=
  slhdsa_euf_cma_fors_tight structural_128s A

#print axioms forsOpenPre_le
#print axioms slhdsa_euf_cma_fors_tight
#print axioms slhdsa_sha2_128s_euf_cma_fors_tight

end Reduction
