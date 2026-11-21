import Reduction.Gen.Sem
import Reduction.ForsTightNonVacuity

/-!
# Wrapper games: source-final-validity SM-DT-DSPR and SM-DT-TCR over a general sampling spec

VCVio's `SM_DT_DSPR_SourceFinalValidity` and `SM_DT_TCR_SourceFinalValidity` games with both
phases of the adversary over `ds + unifSpec` instead of `unifSpec`.  The games themselves (seed
generation, challenge/collection oracles with the final-validity monitor, final predicates) are
VCVio's, run over the general interface by `liftR` / `runG`.

* DSPR: `DsprFVAdversaryG`, `dsprRunG` (the common run), the two final predicates `dsprWin`
  (guess correct) and `dsprSPWin` (second preimage exists) on the same run, `dsprExperimentG`,
  `dsprSPExperimentG`, `dsprSuccessG`, `dsprSPProbabilityG`,
  `dsprAdvantageG = dsprSuccessG - dsprSPProbabilityG`;
* TCR: `TcrFVAdversaryG`, `tcrFVWin`, `tcrFVExperimentG`, `tcrFVAdvantageG`;
* `.ofClassical` and coincidence: `dsprSuccessG_ofClassical`, `dsprSPProbabilityG_ofClassical`,
  `dsprAdvantageG_ofClassical`, `tcrFVAdvantageG_ofClassical`;
* `≤ 1`: `dsprSuccessG_le_one`, `dsprSPProbabilityG_le_one`, `dsprAdvantageG_le_one`,
  `tcrFVAdvantageG_le_one`;
* non-vacuity through `ofClassical`: `forsTcr_trivial_advG_zero`, `forsTcrCollider_advG_one`,
  `forsDspr_trivial_advG_zero`, `forsDsprGuesser_advG_one`,
  `forsDsprGuesser_advG_zero_of_collision`.
-/

open OracleComp OracleSpec ENNReal TweakableHash SLHDSA SLHDSA.Security

namespace Reduction.Gen

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {ι PkSeed Tweak M Y : Type}

/-! ## SM-DT-DSPR -/

/-- A source-final-validity SM-DT-DSPR adversary whose two phases may sample from `ds`. -/
structure DsprFVAdversaryG (prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y) where
  /-- Private state passed from target selection to prediction. -/
  State : Type
  /-- Select targets: general sampling, challenge and collection oracles, no seed. -/
  choose : OracleComp ((ds + unifSpec) +
    (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)) State
  /-- After the seed is revealed: a target index and a prediction. -/
  guess : State → PkSeed → OracleComp (gSpec ds) (ℕ × Bool)

/-- A source-final-validity SM-DT-TCR adversary whose two phases may sample from `ds`. -/
structure TcrFVAdversaryG (prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Select targets: general sampling, challenge and collection oracles, no seed. -/
  choose : OracleComp ((ds + unifSpec) +
    (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)) State
  /-- Given the seed: a target index and a colliding message. -/
  forge : State → PkSeed → OracleComp (gSpec ds) (ℕ × M)

/-- A classical DSPR adversary as an adversary over the general interface. -/
def DsprFVAdversaryG.ofClassical {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_SourceFinalValidity.Adversary prob) : DsprFVAdversaryG ds prob where
  State := adv.State
  choose := embed ds adv.choose
  guess st pk := liftR ds (adv.guess st pk)

/-- A classical TCR adversary as an adversary over the general interface. -/
def TcrFVAdversaryG.ofClassical {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_SourceFinalValidity.Adversary prob) : TcrFVAdversaryG ds prob where
  State := adv.State
  choose := embed ds adv.choose
  forge st pk := liftR ds (adv.forge st pk)

variable [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]

/-- Final predicate of the DSPR experiment: valid run, existing target, correct prediction. -/
def dsprWin [Fintype M] (prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) (st : SM_DT_DSPR_SourceFinalValidity.State Tweak M) (jb : ℕ × Bool) : Bool :=
  match st.challenges[jb.1]? with
  | none => false
  | some (t, m) => st.valid && decide (SecondPreimageExists prob.th pk t m ↔ jb.2 = true)

/-- Final predicate of the `SPprob` baseline: valid run, existing target with a second preimage
(the guessed bit is ignored). -/
def dsprSPWin [Fintype M] (prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) (st : SM_DT_DSPR_SourceFinalValidity.State Tweak M) (jb : ℕ × Bool) : Bool :=
  match st.challenges[jb.1]? with
  | none => false
  | some (t, m) => st.valid && decide (SecondPreimageExists prob.th pk t m)

/-- Final predicate of the TCR experiment. -/
def tcrFVWin (prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) (st : SM_DT_TCR_SourceFinalValidity.State Tweak M) (jm : ℕ × M) : Bool :=
  match st.challenges[jm.1]? with
  | none => false
  | some (t, mj) =>
    st.valid && decide (jm.2 ≠ mj ∧ prob.th.eval pk t jm.2 = prob.th.eval pk t mj)

/-- The run shared by the DSPR experiment and its `SPprob` baseline, with final predicate `win`. -/
noncomputable def dsprRunG {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (win : PkSeed → SM_DT_DSPR_SourceFinalValidity.State Tweak M → ℕ × Bool → Bool)
    (adv : DsprFVAdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  liftR ds prob.th.seedGen >>= fun pk ↦
    runG ds (SM_DT_DSPR_SourceFinalValidity.oracles prob pk) adv.choose .initial >>= fun r ↦
      adv.guess r.1 pk >>= fun jb ↦ pure (win pk r.2 jb)

/-- The DSPR experiment for adversaries over the general sampling interface. -/
noncomputable def dsprExperimentG [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  dsprRunG ds (dsprWin prob) adv

/-- The `SPprob` baseline experiment: the same run, the other final predicate. -/
noncomputable def dsprSPExperimentG [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  dsprRunG ds (dsprSPWin prob) adv

/-- Raw DSPR prediction success. -/
noncomputable def dsprSuccessG [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (dsprExperimentG ds adv)

/-- The `SPprob` baseline probability. -/
noncomputable def dsprSPProbabilityG [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (dsprSPExperimentG ds adv)

/-- SM-DT-DSPR advantage: the truncated difference `Success − SPProbability` (as VCVio). -/
noncomputable def dsprAdvantageG [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : ℝ≥0∞ :=
  dsprSuccessG ds adv - dsprSPProbabilityG ds adv

/-- The TCR experiment for adversaries over the general sampling interface. -/
noncomputable def tcrFVExperimentG
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : TcrFVAdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  liftR ds prob.th.seedGen >>= fun pk ↦
    runG ds (SM_DT_TCR_SourceFinalValidity.oracles prob pk) adv.choose .initial >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦ pure (tcrFVWin prob pk r.2 jm)

/-- The TCR advantage of an adversary over the general sampling interface. -/
noncomputable def tcrFVAdvantageG
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : TcrFVAdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (tcrFVExperimentG ds adv)

/-! ## VCVio's experiments in the shape of the wrapper experiments -/

theorem dspr_experiment_eq [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.experiment adv =
      prob.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles prob pk) adv.choose).run .initial >>=
          fun r ↦ adv.guess r.1 pk >>= fun jb ↦ pure (dsprWin prob pk r.2 jb) := by
  unfold SM_DT_DSPR_SourceFinalValidity.experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ bind_congr fun jb ↦ ?_
  unfold dsprWin
  rcases r with ⟨st, gs⟩
  rcases jb with ⟨j, b⟩
  dsimp only
  split <;> rename_i h <;> simp [h]

theorem dspr_spExperiment_eq [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.spExperiment adv =
      prob.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles prob pk) adv.choose).run .initial >>=
          fun r ↦ adv.guess r.1 pk >>= fun jb ↦ pure (dsprSPWin prob pk r.2 jb) := by
  unfold SM_DT_DSPR_SourceFinalValidity.spExperiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ bind_congr fun jb ↦ ?_
  unfold dsprSPWin
  rcases r with ⟨st, gs⟩
  rcases jb with ⟨j, b⟩
  dsimp only
  split <;> rename_i h <;> simp [h]

theorem tcrFV_experiment_eq
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_SourceFinalValidity.Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.experiment adv =
      prob.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles prob pk) adv.choose).run .initial >>=
          fun r ↦ adv.forge r.1 pk >>= fun jm ↦ pure (tcrFVWin prob pk r.2 jm) := by
  unfold SM_DT_TCR_SourceFinalValidity.experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ bind_congr fun jm ↦ ?_
  unfold tcrFVWin
  rcases r with ⟨st, gs⟩
  rcases jm with ⟨j, m⟩
  dsimp only
  split <;> rename_i h <;> simp [h]

/-! ## Coincidence on classical adversaries -/

/-- **Coincidence (program level)**, DSPR experiment. -/
theorem dsprExperimentG_ofClassical [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    dsprExperimentG ds (DsprFVAdversaryG.ofClassical ds adv) =
      liftR ds (SM_DT_DSPR_SourceFinalValidity.experiment adv) := by
  rw [dspr_experiment_eq]
  simp only [dsprExperimentG, dsprRunG, DsprFVAdversaryG.ofClassical, runG_embed, liftR_bind,
    liftR_pure]

/-- **Coincidence (program level)**, `SPprob` baseline. -/
theorem dsprSPExperimentG_ofClassical [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    dsprSPExperimentG ds (DsprFVAdversaryG.ofClassical ds adv) =
      liftR ds (SM_DT_DSPR_SourceFinalValidity.spExperiment adv) := by
  rw [dspr_spExperiment_eq]
  simp only [dsprSPExperimentG, dsprRunG, DsprFVAdversaryG.ofClassical, runG_embed, liftR_bind,
    liftR_pure]

/-- **Coincidence (program level)**, TCR experiment. -/
theorem tcrFVExperimentG_ofClassical
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_SourceFinalValidity.Adversary prob) :
    tcrFVExperimentG ds (TcrFVAdversaryG.ofClassical ds adv) =
      liftR ds (SM_DT_TCR_SourceFinalValidity.experiment adv) := by
  rw [tcrFV_experiment_eq]
  simp only [tcrFVExperimentG, TcrFVAdversaryG.ofClassical, runG_embed, liftR_bind, liftR_pure]

/-- **Coincidence.** `Success` of VCVio's DSPR game. -/
theorem dsprSuccessG_ofClassical [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    dsprSuccessG ds (DsprFVAdversaryG.ofClassical ds D) =
      SM_DT_DSPR_SourceFinalValidity.Success D := by
  rw [dsprSuccessG, dsprExperimentG_ofClassical, prG_liftR]
  rfl

/-- **Coincidence.** `SPProbability` of VCVio's DSPR game. -/
theorem dsprSPProbabilityG_ofClassical [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    dsprSPProbabilityG ds (DsprFVAdversaryG.ofClassical ds D) =
      SM_DT_DSPR_SourceFinalValidity.SPProbability D := by
  rw [dsprSPProbabilityG, dsprSPExperimentG_ofClassical, prG_liftR]
  rfl

/-- **Coincidence.** `advantage` of VCVio's DSPR game. -/
theorem dsprAdvantageG_ofClassical [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (D : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    dsprAdvantageG ds (DsprFVAdversaryG.ofClassical ds D) =
      SM_DT_DSPR_SourceFinalValidity.advantage D := by
  rw [dsprAdvantageG, dsprSuccessG_ofClassical, dsprSPProbabilityG_ofClassical]
  rfl

/-- **Coincidence.** `advantage` of VCVio's source-final-validity TCR game. -/
theorem tcrFVAdvantageG_ofClassical
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (T : SM_DT_TCR_SourceFinalValidity.Adversary prob) :
    tcrFVAdvantageG ds (TcrFVAdversaryG.ofClassical ds T) =
      SM_DT_TCR_SourceFinalValidity.advantage T := by
  rw [tcrFVAdvantageG, tcrFVExperimentG_ofClassical, prG_liftR]
  rfl

/-! ## Bounds -/

theorem dsprSuccessG_le_one [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : dsprSuccessG ds adv ≤ 1 :=
  prG_le_one ds _

theorem dsprSPProbabilityG_le_one [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : dsprSPProbabilityG ds adv ≤ 1 :=
  prG_le_one ds _

theorem dsprAdvantageG_le_one [Fintype M]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : DsprFVAdversaryG ds prob) : dsprAdvantageG ds adv ≤ 1 :=
  tsub_le_self.trans (dsprSuccessG_le_one ds adv)

theorem tcrFVAdvantageG_le_one
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : TcrFVAdversaryG ds prob) : tcrFVAdvantageG ds adv ≤ 1 :=
  prG_le_one ds _

/-! ## Non-vacuity (through `ofClassical`) -/

section NonVacuity

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y]

/-- The FORS SM-TCR wrapper game can be lost. -/
theorem forsTcr_trivial_advG_zero (pkSeedDist : ProbComp prims.PkSeed) :
    tcrFVAdvantageG ds (TcrFVAdversaryG.ofClassical ds
      (⟨Unit, pure (), fun _ _ ↦ pure (0, default)⟩ :
        SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist))) = 0 := by
  rw [tcrFVAdvantageG_ofClassical]
  exact forsTcr_trivial_adv_zero pkSeedDist

/-- The FORS SM-TCR wrapper game can be won (seed-independent collision of `F`). -/
theorem forsTcrCollider_advG_one (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < openPreTargets vp) (t : prims.AdrsKey) (x y : prims.Y) (hne : y ≠ x)
    (hcol : ∀ pk, prims.Thash pk t [y] = prims.Thash pk t [x]) :
    tcrFVAdvantageG ds (TcrFVAdversaryG.ofClassical ds
      (forsTcrCollider (vp := vp) pkSeedDist t x y)) = 1 := by
  rw [tcrFVAdvantageG_ofClassical]
  exact forsTcrCollider_adv_one pkSeedDist h0 t x y hne hcol

variable [Fintype prims.Y]

/-- The FORS SM-DSPR wrapper game can be lost. -/
theorem forsDspr_trivial_advG_zero (pkSeedDist : ProbComp prims.PkSeed) :
    dsprAdvantageG ds (DsprFVAdversaryG.ofClassical ds
      (⟨Unit, pure (), fun _ _ ↦ pure (0, false)⟩ :
        SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist))) = 0 := by
  rw [dsprAdvantageG_ofClassical]
  exact forsDspr_trivial_adv_zero pkSeedDist

/-- The FORS SM-DSPR wrapper game can be won (`F(pk, t, ·)` injective at `x`). -/
theorem forsDsprGuesser_advG_one (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < openPreTargets vp) (t : prims.AdrsKey) (x : prims.Y)
    (hinj : ∀ pk y, prims.Thash pk t [x] = prims.Thash pk t [y] → x = y) :
    dsprAdvantageG ds (DsprFVAdversaryG.ofClassical ds
      (forsDsprGuesser (vp := vp) pkSeedDist t x false)) = 1 := by
  rw [dsprAdvantageG_ofClassical]
  exact forsDsprGuesser_adv_one pkSeedDist h0 t x hinj

/-- The baseline subtraction is effective in the wrapper game as well. -/
theorem forsDsprGuesser_advG_zero_of_collision (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < openPreTargets vp) (t : prims.AdrsKey) (x y : prims.Y) (hne : x ≠ y)
    (hcol : ∀ pk, prims.Thash pk t [x] = prims.Thash pk t [y]) :
    dsprAdvantageG ds (DsprFVAdversaryG.ofClassical ds
      (forsDsprGuesser (vp := vp) pkSeedDist t x true)) = 0 := by
  rw [dsprAdvantageG_ofClassical]
  exact forsDsprGuesser_adv_zero_of_collision pkSeedDist h0 t x y hne hcol

end NonVacuity

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms dsprSuccessG_ofClassical
#print axioms dsprSPProbabilityG_ofClassical
#print axioms dsprAdvantageG_ofClassical
#print axioms tcrFVAdvantageG_ofClassical
#print axioms forsTcrCollider_advG_one
#print axioms forsDsprGuesser_advG_one
#print axioms forsDsprGuesser_advG_zero_of_collision
end Axioms
