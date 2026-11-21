import Reduction.TcrMemoHeadline

/-!
# The headline theorems in linear (signed-pair) form (package W7)

The final theorems `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_memo`
(`Reduction/TcrMemoHeadline.lean`) bound the forger's advantage by a sum in which four terms are
*distinguishing* advantages: `prfAdvantage` (twice), `SM_DT_UD_Advantage` — absolute differences
`|Pr[real] − Pr[ideal]|` — and `SM_DT_DSPR_SourceFinalValidity.advantage`, the truncated
difference `Pr[DSPR] − Pr[SPprob]`.  Such terms do not commute with averaging over a parameter
of the hash functions.  This file states the same theorems with every distinguishing advantage
replaced by the signed pair of probabilities it is the difference of, additively in `ℝ≥0∞`
(no subtraction anywhere):

`Adv + [Pr[PRF ideal] + Pr[PRF_msg ideal] + Pr[SPprob] + (w−2)·Pr[UD ideal]]
   ≤ [Pr[PRF real] + Pr[PRF_msg real] + Adv^ITSR + (Pr[DSPR] + 3·Adv^TCR_F) + Σ₄ Adv^TCR_class
      + (w−2)·Pr[UD real] + Adv^PRE + Adv^TCR_chain]`.

Contents.

* Named probabilities: `prfRealPr`, `prfIdealPr` (game `skPrfC`), `msgRealPr`, `msgIdealPr`
  (game `msgPrf`); VCVio's `SM_DT_UD_RealSuccess`, `SM_DT_UD_IdealSuccess`,
  `SM_DT_DSPR_SourceFinalValidity.Success`, `.SPProbability` are used as they are.  Each
  existing advantage is the absolute / truncated difference of its pair by `rfl`
  (`prfAdvantage_eq_absDiff`, `msgPrfAdvantage_eq_absDiff`, `udAdvantage_eq_absDiff`,
  `dsprAdvantage_eq_sub`); every named probability is `≤ 1` (`*_le_one`).
* Hops as *equalities* of probabilities (the game before is the real world, the game after the
  ideal world of the distinguisher): `prfRealPr_bPrfC`, `prfIdealPr_bPrfC`,
  `msgRealPr_bPrfMsgL`, `msgIdealPr_bPrfMsgL` (EUF); `prfRealPr_bPrfWC`, `prfIdealPr_bPrfWC`,
  `msgRealPr_bPrfMsgWL`, `msgIdealPr_bPrfMsgWL` (SUF, any final check `w`).
* UD hybrid, exact telescoping identity for the single adversary `rUd pkSeedDist W`:
  `wotsUD_telescope`; per-index forms `udRealSuccess_rUd_sum`, `udIdealSuccess_rUd_sum`,
  `udFixed_prTrue`.
* DSPR step without truncation: `ForsTight.openPRE_add_spprob_le`, `forsOpenPre_add_spprob_le`.
* Linear headlines `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_linear` (+ `_explicit` for the
  two internal ones, + `slhdsa_sha2_128s_*_final_linear`).
* The absolute-value headlines as corollaries: `boundFinalTight_of_linear` and
  `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_memo_of_linear` (right-hand sides exactly those
  of `slhdsa_*_final_memo`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MeasureTheory

/-! ## The DSPR step without truncation (generic) -/

namespace Reduction.ForsTight

open TweakableHash
open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity

set_option linter.unusedSectionVars false

variable {ι PkSeed Tweak M Y : Type}
variable [DecidableEq Tweak] [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y]

/-- **SM-DT-OpenPRE from SM-DT-DSPR and SM-DT-TCR, untruncated additive form.**  For every
OpenPRE problem with uniform hidden inputs and every OpenPRE adversary `adv`,

`Pr[OpenPRE(adv)] + Pr[SPprob(toDSPR adv)] ≤ Pr[DSPR(toDSPR adv)] + 3 · Adv^{TCR}(toTCR adv)`.

This is what the proof of `openPRE_le_dspr_add_three_tcr` establishes before its last step
(there `Pr[DSPR] ≤ (Pr[DSPR] − Pr[SPprob]) + Pr[SPprob]` is used and `Pr[SPprob]` cancelled);
the truncation absorbs no case.  The truncated statement follows from this one, not
conversely. -/
theorem openPRE_add_spprob_le [SampleableType M] {prob : Problem ι PkSeed Tweak M Y}
    (hU : prob.HasUniformInputs) (adv : Adversary prob) :
    advantage adv + SM_DT_DSPR_SourceFinalValidity.SPProbability (toDSPR adv) ≤
      SM_DT_DSPR_SourceFinalValidity.Success (toDSPR adv) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTCR adv) := by
  unfold advantage
    SM_DT_DSPR_SourceFinalValidity.Success SM_DT_DSPR_SourceFinalValidity.SPProbability
    SM_DT_TCR_SourceFinalValidity.advantage
  rw [experiment_eq, tcr_experiment_eq, dspr_experiment_eq, sp_experiment_eq]
  have hE := prE1_le_prE2 hU adv
  let _ : MeasurableSpace (Raw PkSeed Tweak M) := ⊤
  simp only [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)] at hE ⊢
  generalize 𝒟[raw adv] = μ at hE ⊢
  set W := pred prob.numTargets (cW prob.th) ⁻¹' {true} with hW
  set S := pred prob.numTargets (cS prob.th) ⁻¹' {true} with hS
  set D := pred prob.numTargets (cD prob.th) ⁻¹' {true} with hD
  set T := pred prob.numTargets (cT prob.th) ⁻¹' {true} with hT
  set E1 := pred prob.numTargets (cE1 prob.th) ⁻¹' {true} with hE1
  set E2 := pred prob.numTargets (cE2 prob.th) ⁻¹' {true} with hE2
  have hmem : ∀ (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool) (r : Raw PkSeed Tweak M),
      r ∈ pred prob.numTargets c ⁻¹' {true} ↔
        ∃ t x, r.2.2.1[r.2.2.2.1.1]? = some (t, x) ∧
          (recAll prob.numTargets r.2.1 r.2.2.1).valid = true ∧
          c r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2 = true := by
    rintro c ⟨pk, st, tg, ⟨j, m⟩, op⟩
    exact pred_eq_true_iff _ _ _ _ _ _ _ _
  have key : ∀ (pk : PkSeed) (t : Tweak) (x : M) (j : ℕ) (m : M) (op : List ℕ),
      (cS prob.th pk t x j m op = true ∨ cW prob.th pk t x j m op = true) →
        cD prob.th pk t x j m op = true ∨ cE1 prob.th pk t x j m op = true := by
    intro pk t x j m op h
    simp only [cS, cW, cD, cE1, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    by_cases hspe : SecondPreimageExists prob.th pk t x
    · by_cases hb : x ≠ m ∨ j ∈ op
      · exact Or.inl ⟨fun _ => hb, fun _ => hspe⟩
      · rw [not_or, not_not] at hb
        exact Or.inr ⟨hb.2, hb.1.symm, hspe⟩
    · rcases h with h | ⟨hop, heq⟩
      · exact absurd h hspe
      · refine Or.inl ⟨fun h' => absurd h' hspe, fun hb => ?_⟩
        rcases hb with hne | hin
        · exact absurd ⟨m, hne, heq.symm⟩ hspe
        · exact absurd hin hop
  have h2 : W ∪ S ⊆ D ∪ E1 := by
    intro r hr
    have : ∃ t x, r.2.2.1[r.2.2.2.1.1]? = some (t, x) ∧
        (recAll prob.numTargets r.2.1 r.2.2.1).valid = true ∧
        (cS prob.th r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2 = true ∨
          cW prob.th r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2 = true) := by
      rcases hr with hr | hr
      · obtain ⟨t, x, h1, h2, h3⟩ := (hmem _ r).1 hr
        exact ⟨t, x, h1, h2, Or.inr h3⟩
      · obtain ⟨t, x, h1, h2, h3⟩ := (hmem _ r).1 hr
        exact ⟨t, x, h1, h2, Or.inl h3⟩
    obtain ⟨t, x, h1, h2, h3⟩ := this
    rcases key _ _ _ _ _ _ h3 with h | h
    · exact Or.inl ((hmem _ r).2 ⟨t, x, h1, h2, h⟩)
    · exact Or.inr ((hmem _ r).2 ⟨t, x, h1, h2, h⟩)
  have h1 : W ∩ S ⊆ T ∪ E1 := by
    intro r hr
    obtain ⟨t, x, hg, hv, hw⟩ := (hmem _ r).1 hr.1
    obtain ⟨t', x', hg', -, hs⟩ := (hmem _ r).1 hr.2
    rw [hg] at hg'
    simp only [Option.some.injEq, Prod.mk.injEq] at hg'
    obtain ⟨rfl, rfl⟩ := hg'
    simp only [cW, cS, Bool.and_eq_true, decide_eq_true_eq] at hw hs
    by_cases hm : r.2.2.2.1.2 = x
    · exact Or.inr ((hmem _ r).2 ⟨t, x, hg, hv, by
        simp only [cE1, decide_eq_true_eq]; exact ⟨hw.1, hm, hs⟩⟩)
    · exact Or.inl ((hmem _ r).2 ⟨t, x, hg, hv, by
        simp only [cT, decide_eq_true_eq]; exact ⟨hm, hw.2⟩⟩)
  have h3 : E2 ⊆ T := by
    intro r hr
    obtain ⟨t, x, hg, hv, hc⟩ := (hmem _ r).1 hr
    simp only [cE2, decide_eq_true_eq] at hc
    exact (hmem _ r).2 ⟨t, x, hg, hv, by simp only [cT, decide_eq_true_eq]; exact hc.2⟩
  have hsum : μ W + μ S ≤ μ D + μ T + 2 * μ E1 :=
    calc μ W + μ S = μ (W ∪ S) + μ (W ∩ S) :=
          (measure_union_add_inter W MeasurableSet.of_discrete).symm
      _ ≤ μ (D ∪ E1) + μ (T ∪ E1) := add_le_add (measure_mono h2) (measure_mono h1)
      _ ≤ (μ D + μ E1) + (μ T + μ E1) :=
          add_le_add (measure_union_le _ _) (measure_union_le _ _)
      _ = μ D + μ T + 2 * μ E1 := by ring
  have hE1T : μ E1 ≤ μ T := hE.trans (measure_mono h3)
  calc μ W + μ S ≤ μ D + μ T + 2 * μ E1 := hsum
    _ ≤ μ D + μ T + 2 * μ T := by gcongr
    _ = μ D + 3 * μ T := by ring

end Reduction.ForsTight

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

-- as in `Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-! ## Named probabilities -/

/-- `Pr[B outputs 1]` in the **real** world of the PRF game `skPrfC vp prims` (secret-key
address domain): the oracle is `(PK.seed, a) ↦ PRF(PK.seed, k, a)`, `k` uniform.
VCVio: `(skPrfC vp prims).prfRealExperiment B`. -/
noncomputable def prfRealPr (B : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) :
    ℝ≥0∞ :=
  𝒟[(skPrfC vp prims).prfRealExperiment B] {true}

/-- `Pr[B outputs 1]` in the **ideal** world of the PRF game on `PK.seed × SkAdrs vp`: the oracle
is a lazily sampled random function.  VCVio: `PRFScheme.prfIdealExperiment B`. -/
noncomputable def prfIdealPr (B : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) :
    ℝ≥0∞ :=
  𝒟[PRFScheme.prfIdealExperiment B] {true}

/-- `Pr[B outputs 1]` in the **real** world of the PRF game `msgPrf vp prims`: the oracle is
`(opt_rand, M) ↦ PRF_msg(k, opt_rand, M)`, `k` uniform. -/
noncomputable def msgRealPr (B : MsgPrfAdv prims) : ℝ≥0∞ :=
  𝒟[(msgPrf vp prims).prfRealExperiment B] {true}

/-- `Pr[B outputs 1]` in the **ideal** world of the `PRF_msg` game: lazily sampled random
function on `Y × List Byte`. -/
noncomputable def msgIdealPr (B : MsgPrfAdv prims) : ℝ≥0∞ :=
  𝒟[PRFScheme.prfIdealExperiment B] {true}

/-! ### Ties to the VCVio advantages (all by `rfl`) -/

/-- `prfAdvantage` on `skPrfC` is `|prfRealPr − prfIdealPr|`. -/
theorem prfAdvantage_eq_absDiff
    (B : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) :
    (skPrfC vp prims).prfAdvantage B = ENNReal.absDiff (prfRealPr B) (prfIdealPr B) := rfl

/-- `prfAdvantage` on `msgPrf` is `|msgRealPr − msgIdealPr|`. -/
theorem msgPrfAdvantage_eq_absDiff (B : MsgPrfAdv prims) :
    (msgPrf vp prims).prfAdvantage B = ENNReal.absDiff (msgRealPr B) (msgIdealPr B) := rfl

/-- `SM_DT_UD_Advantage` is `|SM_DT_UD_RealSuccess − SM_DT_UD_IdealSuccess|`. -/
theorem udAdvantage_eq_absDiff {ι PkSeed Tweak M M' Y : Type} [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (B : SM_DT_UD_Adversary prob) :
    SM_DT_UD_Advantage B =
      ENNReal.absDiff (SM_DT_UD_RealSuccess B) (SM_DT_UD_IdealSuccess B) := rfl

/-- The SM-DSPR advantage is the truncated difference `Success − SPProbability`. -/
theorem dsprAdvantage_eq_sub {ι PkSeed Tweak M Y : Type} [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.advantage D =
      SM_DT_DSPR_SourceFinalValidity.Success D -
        SM_DT_DSPR_SourceFinalValidity.SPProbability D := rfl

/-- One-sided consequences used to recover the absolute-value statements. -/
theorem prfRealPr_le (B : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) :
    prfRealPr B ≤ prfIdealPr B + (skPrfC vp prims).prfAdvantage B :=
  MeasureTheory.Measure.apply_true_le_add_boolDist _ _

theorem msgRealPr_le (B : MsgPrfAdv prims) :
    msgRealPr B ≤ msgIdealPr B + (msgPrf vp prims).prfAdvantage B :=
  MeasureTheory.Measure.apply_true_le_add_boolDist _ _

theorem udRealSuccess_le {ι PkSeed Tweak M M' Y : Type} [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (B : SM_DT_UD_Adversary prob) :
    SM_DT_UD_RealSuccess B ≤ SM_DT_UD_IdealSuccess B + SM_DT_UD_Advantage B :=
  MeasureTheory.Measure.apply_true_le_add_boolDist _ _

theorem dsprSuccess_le {ι PkSeed Tweak M Y : Type} [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.Success D ≤
      SM_DT_DSPR_SourceFinalValidity.SPProbability D +
        SM_DT_DSPR_SourceFinalValidity.advantage D :=
  le_add_tsub

/-! ### Sanity: every named probability is at most `1` -/

theorem prTrue_le_one' (g : ProbComp Bool) : 𝒟[g] {true} ≤ 1 := prob_le_one

theorem prfRealPr_le_one (B : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) :
    prfRealPr B ≤ 1 := prTrue_le_one' _

theorem prfIdealPr_le_one (B : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) :
    prfIdealPr B ≤ 1 := prTrue_le_one' _

theorem msgRealPr_le_one (B : MsgPrfAdv prims) : msgRealPr B ≤ 1 := prTrue_le_one' _

theorem msgIdealPr_le_one (B : MsgPrfAdv prims) : msgIdealPr B ≤ 1 := prTrue_le_one' _

theorem udRealSuccess_le_one {ι PkSeed Tweak M M' Y : Type} [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (B : SM_DT_UD_Adversary prob) :
    SM_DT_UD_RealSuccess B ≤ 1 := prTrue_le_one' _

theorem udIdealSuccess_le_one {ι PkSeed Tweak M M' Y : Type} [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (B : SM_DT_UD_Adversary prob) :
    SM_DT_UD_IdealSuccess B ≤ 1 := prTrue_le_one' _

theorem dsprSuccess_le_one {ι PkSeed Tweak M Y : Type} [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.Success D ≤ 1 := prTrue_le_one' _

theorem dsprSPProbability_le_one {ι PkSeed Tweak M Y : Type} [Fintype M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.SPProbability D ≤ 1 := prTrue_le_one' _

/-! ## PRF hop on `skPrfC`: the two worlds, as equalities -/

section Generic

variable (pkSeedDist)
variable (rest : prims.PkSeed →
  OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool)

/-- Real world of the domain-restricting wrapper (the first half of the proof of
`prfAdvantageC_eq_of`): the same program as the real world of the unwrapped distinguisher in the
old game. -/
theorem prfRealExperimentC_eq_of
    (hq : ∀ s, Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = s ∧ SkDom vp d.2} (rest s)) :
    (skPrfC vp prims).prfRealExperiment
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (seedThen pkSeedDist rest)) =
      (skPrf vp prims).prfRealExperiment (seedThen pkSeedDist rest) := by
  unfold PRFScheme.prfRealExperiment
  refine bind_congr fun k => ?_
  change simulateQ (Tables.fnImpl fun d : prims.PkSeed × SkAdrs vp => prims.PRF d.1 k d.2.val) _ =
    simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => prims.PRF d.1 k d.2) _
  rw [restrict_liftM_bind]
  unfold seedThen
  rw [simulateQ_bind, simulateQ_bind, Tables.simulateQ_fnImpl_liftM,
    Tables.simulateQ_fnImpl_liftM]
  exact bind_congr fun s => simulateQ_fnImpl_wrapped_of rest hq s _ _ fun _ _ => rfl

/-- Ideal world of the domain-restricting wrapper (the second half of the proof of
`prfAdvantageC_eq_of`): same output distribution as the unwrapped distinguisher. -/
theorem evalDist_prfIdealExperimentC_eq_of
    (hq : ∀ s, Tables.QueriesIn {d : prims.PkSeed × Adrs | d.1 = s ∧ SkDom vp d.2} (rest s)) :
    𝒟[PRFScheme.prfIdealExperiment
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (seedThen pkSeedDist rest))] =
      𝒟[PRFScheme.prfIdealExperiment (seedThen pkSeedDist rest)] := by
  have hold : 𝒟[PRFScheme.prfIdealExperiment
        (seedThen pkSeedDist rest)] =
      𝒟[pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d : prims.PkSeed × Adrs => secretOf vp prims tbl d.2)
          (rest s)] :=
    evalDist_prfIdeal_eq_sampleTable (vp := vp) (prims := prims)
      secIdx_injOn_canonical pkSeedDist id rest
      (fun s _ => (hq s).mono fun t => by
        rcases t with n | d
        · exact fun h => h
        · exact fun h => ⟨h.1, h.2.1⟩)
  have hnew : 𝒟[PRFScheme.prfIdealExperiment
        (simulateQ (Restrict.restrictImpl (skRestrict vp prims))
          (seedThen pkSeedDist rest))] =
      𝒟[pkSeedDist >>= fun s => sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun d : prims.PkSeed × SkAdrs vp => tbl (secIdx d.2.val))
          (simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (rest s))] := by
    unfold PRFScheme.prfIdealExperiment
    rw [restrict_liftM_bind]
    exact Tables.evalDist_prfIdealExperiment_liftM_bind pkSeedDist
      (fun s => simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (rest s))
      (fun _ d => secIdx d.2.val) (fun s => {d : prims.PkSeed × SkAdrs vp | d.1 = s})
      (fun s _ d hd d' hd' h => Prod.ext (hd.trans hd'.symm)
        (Subtype.ext (secIdx_injOn_canonical d.2.2.1 d'.2.2.1 h)))
      (fun s _ => Restrict.queriesIn_restrict _ (S := {d | d.1 = s ∧ SkDom vp d.2})
        (fun d hd d' hd' => by
          rw [skRestrict_of_dom hd.2] at hd'
          cases hd'
          exact hd.1) (hq s))
  rw [hold, hnew]
  refine congrArg _ (bind_congr fun s => bind_congr fun tbl => ?_)
  exact simulateQ_fnImpl_wrapped_of rest hq s _ _ fun _ _ => rfl

end Generic

/-- **EUF, PRF hop, real world**: `Pr[prfReal(bPrfC A) = 1] = Pr[G0]`
(`G0` = the EUF-CMA experiment). -/
theorem prfRealPr_bPrfC (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prfRealPr (bPrfC A) = prTrue (g0 A) :=
  prfRealC_bPrfC hS A

/-- **EUF, PRF hop, ideal world**: `Pr[prfIdeal(bPrfC A) = 1] = Pr[G1]`. -/
theorem prfIdealPr_bPrfC (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prfIdealPr (bPrfC A) = prTrue (g1 A) :=
  prfIdealC_bPrfC hS A

/-- **EUF, PRF_msg hop, real world**: `Pr[prfReal_msg(bPrfMsgL A) = 1] = Pr[G1]`. -/
theorem msgRealPr_bPrfMsgL (A : Forger vp prims optRand pkSeedDist) :
    msgRealPr (Lazy.bPrfMsgL A) = prTrue (g1 A) := by
  unfold msgRealPr
  rw [Lazy.evalDist_prfReal_bPrfMsgL]
  exact prfReal_bPrfMsg A

/-- **EUF, PRF_msg hop, ideal world**: `Pr[prfIdeal_msg(bPrfMsgL A) = 1] = Pr[G2]`. -/
theorem msgIdealPr_bPrfMsgL (A : Forger vp prims optRand pkSeedDist) :
    msgIdealPr (Lazy.bPrfMsgL A) = prTrue (g2 A) := by
  unfold msgIdealPr
  rw [Lazy.evalDist_prfIdeal_bPrfMsgL]
  exact prfIdeal_bPrfMsg A

/-- **SUF, PRF hop, real world**: `Pr[prfReal(bPrfWC w A) = 1] = Pr[Exp_w(real scheme)]`. -/
theorem prfRealPr_bPrfWC (hS : Structural vp prims) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prfRealPr (bPrfWC w A) = prTrue (expW (realAlg vp prims optRand pkSeedDist) w A) := by
  unfold prfRealPr bPrfWC
  rw [bPrfW_eq_bRestW,
    prfRealExperimentC_eq_of pkSeedDist (bRestW w A) (queriesIn_bRestW hS.bounds w A),
    ← bPrfW_eq_bRestW]
  exact prfReal_bPrfW w A

/-- **SUF, PRF hop, ideal world**: `Pr[prfIdeal(bPrfWC w A) = 1] = Pr[Exp_w(table scheme)]`. -/
theorem prfIdealPr_bPrfWC (hS : Structural vp prims) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prfIdealPr (bPrfWC w A) = prTrue (expW (tableAlg vp prims optRand pkSeedDist) w A) := by
  unfold prfIdealPr bPrfWC
  rw [bPrfW_eq_bRestW,
    evalDist_prfIdealExperimentC_eq_of pkSeedDist (bRestW w A) (queriesIn_bRestW hS.bounds w A),
    ← bPrfW_eq_bRestW]
  exact prfIdeal_bPrfW hS w A

/-- **SUF, PRF_msg hop, real world**:
`Pr[prfReal_msg(bPrfMsgWL w A) = 1] = Pr[Exp_w(table scheme)]`. -/
theorem msgRealPr_bPrfMsgWL (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    msgRealPr (Lazy.bPrfMsgWL w A) = prTrue (expW (tableAlg vp prims optRand pkSeedDist) w A) := by
  unfold msgRealPr
  rw [Lazy.evalDist_prfReal_bPrfMsgWL]
  exact prfReal_bPrfMsgW w A

/-- **SUF, PRF_msg hop, ideal world**: `Pr[prfIdeal_msg(bPrfMsgWL w A) = 1] = Pr[G2_w]`. -/
theorem msgIdealPr_bPrfMsgWL (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    msgIdealPr (Lazy.bPrfMsgWL w A) = prTrue (g2W w A) := by
  unfold msgIdealPr
  rw [Lazy.evalDist_prfIdeal_bPrfMsgWL]
  exact prfIdeal_bPrfMsgW w A

/-! ## The UD hybrid, linear -/

/-- **Exact telescoping identity of the undetectability hybrid**, for the single SM-UD adversary
`rUd pkSeedDist W` (which samples the hybrid index uniformly among `w − 2` values):

`Pr[Hyb₀] + (w−2)·Pr[UD ideal world, rUd W = 1] = (w−2)·Pr[UD real world, rUd W = 1] + Pr[Hyb_{w−2}]`.

(At fixed index `k` the real world is `Hyb_k` and the ideal world `Hyb_{k+1}`.)  Holds for every
`w` (for `w ≤ 2` both sides are `Pr[Hyb₀]`). -/
theorem wotsUD_telescope (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) :
    prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 W) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_IdealSuccess (rUd pkSeedDist W) =
      ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_RealSuccess (rUd pkSeedDist W) +
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (vp.params.w - 2) W) := by
  unfold SM_DT_UD_IdealSuccess SM_DT_UD_RealSuccess
  by_cases hw : 3 ≤ vp.params.w
  · rw [udReal_rUd hS pkSeedDist W hw, udIdeal_rUd hS pkSeedDist W hw]
    generalize hp : (fun k => prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) k W)) = p
    have hp' : ∀ k, prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) k W) = p k :=
      fun k => congrFun hp k
    simp only [hp']
    generalize vp.params.w - 2 = n
    rw [← Finset.sum_range_succ, Finset.sum_range_succ', add_comm]
  · have h0 : vp.params.w - 2 = 0 := by omega
    rw [h0]
    simp

/-- Per-index form, real world: `(w−2)·Pr[UD real, rUd W] = Σ_{k<w−2} Pr[Hyb_k]`. -/
theorem udRealSuccess_rUd_sum (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) (hw : 3 ≤ vp.params.w) :
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_RealSuccess (rUd pkSeedDist W) =
      ∑ k ∈ Finset.range (vp.params.w - 2),
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) k W) :=
  udReal_rUd hS pkSeedDist W hw

/-- Per-index form, ideal world: `(w−2)·Pr[UD ideal, rUd W] = Σ_{k<w−2} Pr[Hyb_{k+1}]`. -/
theorem udIdealSuccess_rUd_sum (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (W : WotsGame.Adversary prims) (hw : 3 ≤ vp.params.w) :
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_IdealSuccess (rUd pkSeedDist W) =
      ∑ k ∈ Finset.range (vp.params.w - 2),
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (k + 1) W) :=
  udIdeal_rUd hS pkSeedDist W hw

/-- The SM-UD experiment of `rUd W` with the hybrid index fixed to `k` (`WotsUD.udFixed`) succeeds
with the probability of `Hyb_k` in the real world and of `Hyb_{k+1}` in the ideal world. -/
theorem udFixed_prTrue (hS : Structural vp prims) (pkSeedDist : ProbComp prims.PkSeed)
    (world : SM_DT_UD_World) (k : ℕ) (W : WotsGame.Adversary prims) :
    prTrue (WotsUD.udFixed pkSeedDist world k W) =
      prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) (WotsUD.hidx world k) W) := by
  rw [WotsFinal.prTrue_eq, WotsFinal.prTrue_eq]
  exact (WotsUD.udFixed_eq pkSeedDist hS world k W).prEvent_eq _

/-! ## The DSPR step at the FORS-leaf problem, linear -/

variable [Fintype prims.Y]

/-- **`Pr[OpenPRE(B)] + Pr[SPprob(toDspr B)] ≤ Pr[DSPR(toDspr B)] + 3·Adv^{TCR}_F(toTcr B)`**
for every OpenPRE adversary `B` of the FORS-leaf problem; no truncated subtraction. -/
theorem forsOpenPre_add_spprob_le (B : ForsOpenPreAdv vp prims pkSeedDist) :
    SM_DT_OpenPRE_SourceFinalValidity.advantage B +
        SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr B) ≤
      SM_DT_DSPR_SourceFinalValidity.Success (toDspr B) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr B) :=
  ForsTight.openPRE_add_spprob_le forsOpenPreProblem_uniform B

/-! ## The two sides of the linear bound -/

/-- **Left ("ideal") side of the linear bound**: the ideal-world probabilities of the four
distinguishing terms, `Pr[PRF ideal, B₁] + Pr[PRF_msg ideal, B₂] + Pr[SPprob, D]
+ (w−2)·Pr[UD ideal, B₆]`. -/
noncomputable def linearIdealSide
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist)) : ℝ≥0∞ :=
  prfIdealPr B₁ + msgIdealPr B₂ + SM_DT_DSPR_SourceFinalValidity.SPProbability D +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_IdealSuccess B₆

/-- **Right ("real") side of the linear bound**: `boundFinalTight` with each distinguishing
advantage replaced by the real-world probability of its pair. -/
noncomputable def linearRealSide (pkSeedDist : ProbComp prims.PkSeed)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (T : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist)) : ℝ≥0∞ :=
  prfRealPr B₁ + msgRealPr B₂ +
    KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.Success D +
      3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    (SM_DT_TCR_Advantage C₁ + SM_DT_TCR_Advantage C₂ + SM_DT_TCR_Advantage C₃ +
      SM_DT_TCR_Advantage C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_RealSuccess B₆ +
    SM_DT_PRE_Advantage B₇ +
    SM_DT_TCR_Advantage B₈

/-- The ideal side is finite (at most `w + 1`). -/
theorem linearIdealSide_ne_top
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist)) :
    linearIdealSide B₁ B₂ D B₆ ≠ ⊤ := by
  have h1 := (prfIdealPr_le_one B₁).trans_lt ENNReal.one_lt_top
  have h2 := (msgIdealPr_le_one B₂).trans_lt ENNReal.one_lt_top
  have h3 := (dsprSPProbability_le_one D).trans_lt ENNReal.one_lt_top
  have h4 := (udIdealSuccess_le_one B₆).trans_lt ENNReal.one_lt_top
  unfold linearIdealSide
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨h1.ne, h2.ne⟩, h3.ne⟩,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) h4.ne⟩

/-! ## From the linear form to the absolute-value form -/

private theorem of_linear_arith
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

/-- **The absolute-value bound follows from the linear bound** (any adversaries, any left-hand
quantity): if `adv + linearIdealSide … ≤ linearRealSide …` then `adv ≤ boundFinalTight …`. -/
theorem boundFinalTight_of_linear {adv : ℝ≥0∞}
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))
    (T : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))
    (C₁ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist 1))
    (C₂ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist 2))
    (C₃ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist vp.params.len))
    (C₄ : SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist vp.params.k))
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist))
    (h : adv + linearIdealSide B₁ B₂ D B₆ ≤
      linearRealSide pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈) :
    adv ≤ boundFinalTight pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈ := by
  have hfin := linearIdealSide_ne_top B₁ B₂ D B₆
  unfold linearIdealSide at h hfin
  unfold linearRealSide at h
  unfold boundFinalTight
  exact of_linear_arith (prfRealPr_le B₁) (msgRealPr_le B₂) (dsprSuccess_le D)
    (udRealSuccess_le B₆) hfin h

/-! ## Composition -/

private theorem linear_tail {G i o x h0 hn p t8 n I R S D T : ℝ≥0∞}
    (hG : G ≤ i + o + x + h0) (htel : h0 + n * I = n * R + hn) (hfin : hn ≤ p + t8)
    (hO : o + S ≤ D + 3 * T) :
    G + S + n * I ≤ i + (D + 3 * T) + x + n * R + p + t8 :=
  calc G + S + n * I ≤ (i + o + x + h0) + S + n * I := by gcongr
    _ = i + (o + S) + x + (h0 + n * I) := by ring
    _ ≤ i + (D + 3 * T) + x + (n * R + (p + t8)) := by rw [htel]; gcongr
    _ = _ := by ring

private theorem linear_head {adv r1 i1 r2 i2 G S nI rest : ℝ≥0∞}
    (h0 : adv = r1) (h1 : i1 = r2) (h2 : i2 = G) (ht : G + S + nI ≤ rest) :
    adv + (i1 + i2 + S + nI) ≤ r1 + r2 + rest := by
  subst h0 h1 h2
  calc adv + (i1 + i2 + S + nI) = adv + i1 + (i2 + S + nI) := by ring
    _ ≤ adv + i1 + rest := by gcongr

/-- **Everything after the two PRF hops, linear.**  If `G` (the success probability in `G2`) is
at most the four branch terms (ITSR, FORS OpenPRE, the four class collisions, `Hyb₀` of the WOTS
game), then

`G + Pr[SPprob] + (w−2)·Pr[UD ideal] ≤ Adv^ITSR + (Pr[DSPR] + 3·Adv^TCR_F) + Σ₄ Adv^TCR_class
   + (w−2)·Pr[UD real] + Adv^PRE + Adv^TCR_chain`. -/
theorem g2_tail_linear (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (G : ℝ≥0∞)
    (hG : G ≤ KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
      SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) + tcrSplitSumS A +
      prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (Lazy.bWotsS A))) :
    G + SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (Lazy.bOpenPreS A)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_IdealSuccess (rUd pkSeedDist (Lazy.bWotsS A)) ≤
      KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (Lazy.bOpenPreS A)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (Lazy.bOpenPreS A))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 A) + SM_DT_TCR_Advantage (bTcrArM 2 A) +
          SM_DT_TCR_Advantage (bTcrArM vp.params.len A) +
          SM_DT_TCR_Advantage (bTcrArM vp.params.k A)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_TCR_Advantage (rTcrT pkSeedDist (Lazy.bWotsS A)) := by
  have hfin := stepWotsFinal hS pkSeedDist (Lazy.bWotsS A)
  unfold StepWotsFinal at hfin
  rw [bTcrArM_advantage_eq_loose hS 1 A, bTcrArM_advantage_eq_loose hS 2 A,
    bTcrArM_advantage_eq_loose hS vp.params.len A, bTcrArM_advantage_eq_loose hS vp.params.k A,
    rTcrT_advantage_eq hS (Lazy.bWotsS A)]
  unfold tcrSplitSumS at hG
  exact linear_tail hG (wotsUD_telescope hS pkSeedDist (Lazy.bWotsS A)) hfin
    (forsOpenPre_add_spprob_le (Lazy.bOpenPreS A))

/-- EUF: `Pr[G2]` is at most the four branch terms. -/
theorem g2_le_branches (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2 A) ≤ KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
      SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) + tcrSplitSumS A +
      prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (Lazy.bWotsS A)) := by
  have h₃ := stepSplit A
  have h₄ := Lazy.stepITSR_lazy A
  have h₅ := Lazy.stepOpenPRE_sparse hS A
  have h₆ := stepTCR_split_sparse hS A
  have h₇ := Lazy.stepWotsEmbed_sparse hS A
  unfold StepSplit at h₃; unfold StepITSR at h₄; unfold StepOpenPRE at h₅
  unfold StepWotsEmbed at h₇
  exact h₃.trans (add_le_add (add_le_add (add_le_add h₄ h₅) h₆) h₇)

/-- Union bound over the four chargeable events of `G2` (sparse table), stopping at `Hyb₀`. -/
theorem g2WithS_le_branches (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (hwin : ∀ pkSeed tbl z, win pkSeed tbl z = true →
      evItsr pkSeed tbl z = true ∨ evOpen pkSeed tbl z = true ∨
        evColl pkSeed tbl z = true ∨ evWots pkSeed tbl z = true) :
    prTrue (g2WithS A win) ≤
      KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) + tcrSplitSumS A +
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (Lazy.bWotsS A)) := by
  have h1 := g2WithS_le_add A win evItsr
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    (fun pkSeed tbl z h => by
      rcases hwin pkSeed tbl z h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; simp)
      · exact Or.inr (by rw [h]; simp))
  have h2 := g2WithS_le_add A
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    evOpen (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z)
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have h3 := g2WithS_le_add A
    (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z) evColl evWots
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  calc prTrue (g2WithS A win)
      ≤ prTrue (g2WithS A evItsr) + (prTrue (g2WithS A evOpen) +
          (prTrue (g2WithS A evColl) + prTrue (g2WithS A evWots))) :=
        h1.trans (add_le_add_right (h2.trans (add_le_add_right h3 _)) _)
    _ ≤ KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
          (SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) +
          (tcrSplitSumS A +
            prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (Lazy.bWotsS A)))) :=
        add_le_add (brS_itsr hS A) (add_le_add (brS_open hS A)
          (add_le_add (brS_coll_split hS A) (brS_wots hS A)))
    _ = _ := by ring

/-- SUF: `Pr[G2_w]` is at most the four branch terms, for every final check `w` implying
`sufCheck`. -/
theorem g2W_le_branches (hS : Structural vp prims) (w : WinCheck vp prims)
    (hw : ∀ pk f log, w pk f log = true → sufCheck pk f log = true)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2W w A) ≤
      KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) + tcrSplitSumS A +
        prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (Lazy.bWotsS A)) := by
  rw [g2W_eq_g2With, prTrue_g2With_eq_sparse hS A _ (winOfCheck_restrict hS w)]
  exact g2WithS_le_branches hS A _ fun pkSeed tbl z h =>
    (sufWin_cases pkSeed tbl z (sufWin_of_sufCheck pkSeed tbl z (hw _ _ _ h))).elim
      (freshWin_cases hS pkSeed tbl z) (sameWin_cases hS pkSeed tbl z)

/-! ## The linear headlines -/

/-- **Standard-model EUF-CMA security of SLH-DSA (internal algorithms), linear form.**  For
every chosen-message forger `A`:

`Adv^{EUF-CMA}(A) + Pr[prfIdeal(bPrfC A)] + Pr[prfIdeal_msg(bPrfMsgL A)]
     + Pr[SPprob(toDspr (bOpenPreS A))] + (w−2)·Pr[UD ideal(rUd (bWotsS A))]
   ≤ Pr[prfReal(bPrfC A)] + Pr[prfReal_msg(bPrfMsgL A)] + Adv^{ITSR}(bItsrL A)
     + (Pr[DSPR(toDspr (bOpenPreS A))] + 3·Adv^{TCR}_F(toTcr (bOpenPreS A)))
     + Σ_{n ∈ {1,2,len,k}} Adv^{TCR}_{Thash|n}(bTcrArM n A)
     + (w−2)·Pr[UD real(rUd (bWotsS A))] + Adv^{PRE}_F(rPre (bWotsS A))
     + Adv^{TCR}_F(rTcrT (bWotsS A))`. -/
theorem slhdsa_euf_cma_final_linear (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
        linearIdealSide (bPrfC A) (Lazy.bPrfMsgL A) (toDspr (Lazy.bOpenPreS A))
          (rUd pkSeedDist (Lazy.bWotsS A)) ≤
      linearRealSide pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) := by
  have ht := g2_tail_linear hS A _ (g2_le_branches hS A)
  have h0 : SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A =
      prfRealPr (bPrfC A) :=
    (unforgeableAdvantage_eq_prTrue_g0 A).trans (prfRealPr_bPrfC hS A).symm
  have h1 : prfIdealPr (bPrfC A) = msgRealPr (Lazy.bPrfMsgL A) :=
    (prfIdealPr_bPrfC hS A).trans (msgRealPr_bPrfMsgL A).symm
  have h2 := msgIdealPr_bPrfMsgL A
  unfold linearIdealSide linearRealSide
  have := linear_head h0 h1 h2 ht
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Standard-model SUF-CMA security of SLH-DSA (internal algorithms), linear form.**  For
every strong forger `S`, with `A := S.toUnforgeableAdversary`:

`Adv^{SUF-CMA}(S) + Pr[prfIdeal(bPrfWC sufCheck A)] + Pr[prfIdeal_msg(bPrfMsgWL sufCheck A)]
     + Pr[SPprob(toDspr (bOpenPreS A))] + (w−2)·Pr[UD ideal(rUd (bWotsS A))]
   ≤ Pr[prfReal(bPrfWC sufCheck A)] + Pr[prfReal_msg(bPrfMsgWL sufCheck A)] + Adv^{ITSR}(bItsrL A)
     + (Pr[DSPR(toDspr (bOpenPreS A))] + 3·Adv^{TCR}_F(toTcr (bOpenPreS A)))
     + Σ_{n ∈ {1,2,len,k}} Adv^{TCR}_{Thash|n}(bTcrArM n A)
     + (w−2)·Pr[UD real(rUd (bWotsS A))] + Adv^{PRE}_F(rPre (bWotsS A))
     + Adv^{TCR}_F(rTcrT (bWotsS A))`. -/
theorem slhdsa_suf_cma_final_linear (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linearIdealSide (bPrfWC sufCheck S.toUnforgeableAdversary)
          (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
          (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
          (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) ≤
      linearRealSide pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArM 1 S.toUnforgeableAdversary) (bTcrArM 2 S.toUnforgeableAdversary)
        (bTcrArM vp.params.len S.toUnforgeableAdversary)
        (bTcrArM vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) := by
  generalize hA : S.toUnforgeableAdversary = A
  have ht := g2_tail_linear hS A _ (g2W_le_branches hS sufCheck (fun _ _ _ h => h) A)
  have h0 : SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S =
      prfRealPr (bPrfWC sufCheck A) := by
    rw [strongAdvantage_eq_expW, hA]
    exact (prfRealPr_bPrfWC hS sufCheck A).symm
  have h1 : prfIdealPr (bPrfWC sufCheck A) = msgRealPr (Lazy.bPrfMsgWL sufCheck A) :=
    (prfIdealPr_bPrfWC hS sufCheck A).trans (msgRealPr_bPrfMsgWL sufCheck A).symm
  have h2 := msgIdealPr_bPrfMsgWL sufCheck A
  unfold linearIdealSide linearRealSide
  have := linear_head h0 h1 h2 ht
  calc _ ≤ _ := this
    _ = _ := by ring

/-- `slhdsa_suf_cma_final_linear` with both sides written out (no `linearIdealSide` /
`linearRealSide`). -/
theorem slhdsa_suf_cma_final_linear_explicit (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        (prfIdealPr (bPrfWC sufCheck S.toUnforgeableAdversary) +
          msgIdealPr (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary) +
          SM_DT_DSPR_SourceFinalValidity.SPProbability
            (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary)) +
          ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
            SM_DT_UD_IdealSuccess (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))) ≤
      prfRealPr (bPrfWC sufCheck S.toUnforgeableAdversary) +
        msgRealPr (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (Lazy.bItsrL S.toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.Success
            (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage
            (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 S.toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 2 S.toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM vp.params.len S.toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM vp.params.k S.toUnforgeableAdversary)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) +
        SM_DT_TCR_Advantage (rTcrT pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) :=
  slhdsa_suf_cma_final_linear hS S

/-- `slhdsa_euf_cma_final_linear` with both sides written out. -/
theorem slhdsa_euf_cma_final_linear_explicit (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
        (prfIdealPr (bPrfC A) + msgIdealPr (Lazy.bPrfMsgL A) +
          SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (Lazy.bOpenPreS A)) +
          ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
            SM_DT_UD_IdealSuccess (rUd pkSeedDist (Lazy.bWotsS A))) ≤
      prfRealPr (bPrfC A) + msgRealPr (Lazy.bPrfMsgL A) +
        KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (Lazy.bOpenPreS A)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (Lazy.bOpenPreS A))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 A) + SM_DT_TCR_Advantage (bTcrArM 2 A) +
          SM_DT_TCR_Advantage (bTcrArM vp.params.len A) +
          SM_DT_TCR_Advantage (bTcrArM vp.params.k A)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
        SM_DT_TCR_Advantage (rTcrT pkSeedDist (Lazy.bWotsS A)) :=
  slhdsa_euf_cma_final_linear hS A

/-- The two sides as functions of the forger (EUF adversaries). -/
noncomputable def linIdealEuf (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  linearIdealSide (bPrfC A) (Lazy.bPrfMsgL A) (toDspr (Lazy.bOpenPreS A))
    (rUd pkSeedDist (Lazy.bWotsS A))

noncomputable def linRealEuf (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  linearRealSide pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

/-- The two sides as functions of the forger (SUF adversaries: `bPrfWC sufCheck A`,
`bPrfMsgWL sufCheck A` in the PRF slots). -/
noncomputable def linIdealSuf (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  linearIdealSide (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (toDspr (Lazy.bOpenPreS A))
    (rUd pkSeedDist (Lazy.bWotsS A))

noncomputable def linRealSuf (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  linearRealSide pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

/-- `∀`-forms. -/
theorem slhdsa_euf_cma_final_linear' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf A ≤
        linRealEuf A :=
  fun A => slhdsa_euf_cma_final_linear hS A

theorem slhdsa_suf_cma_final_linear' (hS : Structural vp prims) :
    ∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
          linIdealSuf S.toUnforgeableAdversary ≤ linRealSuf S.toUnforgeableAdversary :=
  fun S => slhdsa_suf_cma_final_linear hS S

/-- **EUF-CMA of the external pure interface, linear form**: the linear bound at the internal
forger `toInternal A` (only the left `Adv` changes: `Adv_ext(A) ≤ Adv_int(toInternal A)`). -/
theorem slhdsa_pure_euf_cma_final_linear (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (toInternal A) ≤
      linRealEuf (toInternal A) :=
  (add_le_add_left (external_advantage_le A) _).trans
    (slhdsa_euf_cma_final_linear hS (toInternal A))

/-- **SUF-CMA of the external pure interface, linear form**: the linear SUF bound at the
internal forger `toInternal S.toUnforgeableAdversary`. -/
theorem slhdsa_pure_suf_cma_final_linear (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (toInternal S.toUnforgeableAdversary) ≤
      linRealSuf (toInternal S.toUnforgeableAdversary) :=
  (add_le_add_left (external_strong_advantage_le S) _).trans
    (slhdsa_suf_cma_final_linear hS (toInternalS S))

/-! ## The absolute-value headlines as corollaries of the linear ones -/

/-- `slhdsa_suf_cma_final_memo`, re-derived from `slhdsa_suf_cma_final_linear` (same statement). -/
theorem slhdsa_suf_cma_final_memo_of_linear (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArM 1 S.toUnforgeableAdversary) (bTcrArM 2 S.toUnforgeableAdversary)
        (bTcrArM vp.params.len S.toUnforgeableAdversary)
        (bTcrArM vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_suf_cma_final_linear hS S)

/-- `slhdsa_euf_cma_final_memo`, re-derived from `slhdsa_euf_cma_final_linear`. -/
theorem slhdsa_euf_cma_final_memo_of_linear (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_euf_cma_final_linear hS A)

/-- `slhdsa_pure_euf_cma_final_memo'`, re-derived from `slhdsa_pure_euf_cma_final_linear`. -/
theorem slhdsa_pure_euf_cma_final_memo_of_linear (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal A) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_euf_cma_final_linear hS A)

/-- `slhdsa_pure_suf_cma_final_memo'`, re-derived from `slhdsa_pure_suf_cma_final_linear`. -/
theorem slhdsa_pure_suf_cma_final_memo_of_linear (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_suf_cma_final_linear hS S)

/-- The linear sides and the absolute-value bound, as functions of the forger:
`linRealEuf A ≤ betaEufFinalMemo A + linIdealEuf A` (and the same for SUF). -/
theorem linRealEuf_le (A : Forger vp prims optRand pkSeedDist) :
    linRealEuf A ≤ betaEufFinalMemo A + linIdealEuf A := by
  unfold linRealEuf betaEufFinalMemo linIdealEuf linearRealSide boundFinalTight linearIdealSide
  have h1 := prfRealPr_le (bPrfC A)
  have h2 := msgRealPr_le (Lazy.bPrfMsgL A)
  have h3 := dsprSuccess_le (toDspr (Lazy.bOpenPreS A))
  have h4 := udRealSuccess_le (rUd pkSeedDist (Lazy.bWotsS A))
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add h1 h2) le_rfl) (add_le_add h3 le_rfl)) le_rfl)
    (mul_le_mul_right h4 _)) le_rfl) le_rfl) (le_of_eq ?_)
  ring

theorem linRealSuf_le (A : Forger vp prims optRand pkSeedDist) :
    linRealSuf A ≤ betaSufFinalMemo A + linIdealSuf A := by
  unfold linRealSuf betaSufFinalMemo linIdealSuf linearRealSide boundFinalTight linearIdealSide
  have h1 := prfRealPr_le (bPrfWC sufCheck A)
  have h2 := msgRealPr_le (Lazy.bPrfMsgWL sufCheck A)
  have h3 := dsprSuccess_le (toDspr (Lazy.bOpenPreS A))
  have h4 := udRealSuccess_le (rUd pkSeedDist (Lazy.bWotsS A))
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add h1 h2) le_rfl) (add_le_add h3 le_rfl)) le_rfl)
    (mul_le_mul_right h4 _)) le_rfl) le_rfl) (le_of_eq ?_)
  ring

end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction

open TweakableHash

/-- **SUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), linear form.** -/
theorem slhdsa_sha2_128s_suf_cma_final_linear
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf S.toUnforgeableAdversary ≤ linRealSuf S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_linear structural_128s S

/-- **EUF-CMA security of SLH-DSA-SHA2-128s (internal algorithms), linear form.** -/
theorem slhdsa_sha2_128s_euf_cma_final_linear
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf A ≤
      linRealEuf A :=
  slhdsa_euf_cma_final_linear structural_128s A

/-- **EUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, linear form.** -/
theorem slhdsa_sha2_128s_pure_euf_cma_final_linear
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : ExtForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (toInternal A) ≤
      linRealEuf (toInternal A) :=
  slhdsa_pure_euf_cma_final_linear structural_128s A

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s, linear form.** -/
theorem slhdsa_sha2_128s_pure_suf_cma_final_linear
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : ExtStrongForger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (toInternal S.toUnforgeableAdversary) ≤
      linRealSuf (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final_linear structural_128s S

#print axioms ForsTight.openPRE_add_spprob_le
#print axioms forsOpenPre_add_spprob_le
#print axioms wotsUD_telescope
#print axioms udFixed_prTrue
#print axioms prfRealPr_bPrfC
#print axioms prfIdealPr_bPrfC
#print axioms msgRealPr_bPrfMsgL
#print axioms msgIdealPr_bPrfMsgL
#print axioms prfRealPr_bPrfWC
#print axioms prfIdealPr_bPrfWC
#print axioms msgRealPr_bPrfMsgWL
#print axioms msgIdealPr_bPrfMsgWL
#print axioms boundFinalTight_of_linear
#print axioms slhdsa_suf_cma_final_linear
#print axioms slhdsa_euf_cma_final_linear
#print axioms slhdsa_suf_cma_final_linear_explicit
#print axioms slhdsa_euf_cma_final_linear_explicit
#print axioms slhdsa_pure_euf_cma_final_linear
#print axioms slhdsa_pure_suf_cma_final_linear
#print axioms slhdsa_suf_cma_final_memo_of_linear
#print axioms slhdsa_euf_cma_final_memo_of_linear
#print axioms slhdsa_pure_euf_cma_final_memo_of_linear
#print axioms slhdsa_pure_suf_cma_final_memo_of_linear
#print axioms linRealEuf_le
#print axioms linRealSuf_le
#print axioms slhdsa_sha2_128s_suf_cma_final_linear
#print axioms slhdsa_sha2_128s_euf_cma_final_linear
#print axioms slhdsa_sha2_128s_pure_euf_cma_final_linear
#print axioms slhdsa_sha2_128s_pure_suf_cma_final_linear

end Reduction
