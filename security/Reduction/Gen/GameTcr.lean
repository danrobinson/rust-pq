import Reduction.Gen.Sem
import Reduction.TightCaps

/-!
# Wrapper game: SM-TCR with adversaries over a general sampling spec

VCVio's `SM_DT_TCR_Experiment` with both phases of the adversary over `ds + unifSpec` instead of
`unifSpec`.  The game itself (seed generation, challenge and collection oracles, final check) is
VCVio's, run over the general interface by `liftR` / `runG`.

* `SM_DT_TCR_AdversaryG`, `SM_DT_TCR_ExperimentG`, `SM_DT_TCR_AdvantageG`;
* `SM_DT_TCR_AdversaryG.ofClassical` and `SM_DT_TCR_AdvantageG_ofClassical`: on classical
  adversaries the wrapper game is VCVio's game (same advantage);
* non-vacuity: `SM_DT_TCR_AdvantageG_le_one`, and through `ofClassical` every value attained in
  VCVio's game is attained in the wrapper game (`thashArityT_trivial_advG_zero`,
  `thashArityColliderT_advG_one` are in `Reduction/Gen/GameWots.lean`).
-/

open OracleComp OracleSpec ENNReal TweakableHash

namespace Reduction.Gen

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {ι PkSeed Tweak M Y : Type}

/-- An SM-TCR adversary whose two phases may sample from `ds` as well as uniformly. -/
structure SM_DT_TCR_AdversaryG (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Phase 1: challenge and collection oracles, no seed. -/
  choose : OracleComp
    ((ds + unifSpec) + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl)) State
  /-- Phase 2: the seed, no oracle. -/
  forge : State → PkSeed → OracleComp (gSpec ds) (ℕ × M)

variable [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]

/-- The final check of the SM-TCR game. -/
def tcrWin (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (qsChal : List (Tweak × M)) (jm : ℕ × M) : Bool :=
  match qsChal[jm.1]? with
  | none => false
  | some (t, mj) => decide (jm.2 ≠ mj ∧ prob.th.eval pk t jm.2 = prob.th.eval pk t mj)

/-- The SM-TCR experiment for adversaries over the general sampling interface. -/
noncomputable def SM_DT_TCR_ExperimentG {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_AdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  liftR ds prob.th.seedGen >>= fun pk ↦
    runG ds (SM_DT_TCR_oracles prob pk) adv.choose ([], []) >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦ pure (tcrWin prob pk r.2.1 jm)

/-- The SM-TCR advantage of an adversary over the general sampling interface. -/
noncomputable def SM_DT_TCR_AdvantageG {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_AdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (SM_DT_TCR_ExperimentG ds adv)

/-- A classical adversary as an adversary over the general interface. -/
def SM_DT_TCR_AdversaryG.ofClassical {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) : SM_DT_TCR_AdversaryG ds prob where
  State := adv.State
  choose := embed ds adv.choose
  forge st pk := liftR ds (adv.forge st pk)

/-- VCVio's experiment in the shape of the wrapper experiment. -/
theorem SM_DT_TCR_Experiment_eq {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_Experiment adv =
      prob.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_TCR_oracles prob pk) adv.choose).run ([], []) >>= fun r ↦
          adv.forge r.1 pk >>= fun jm ↦ pure (tcrWin prob pk r.2.1 jm) := by
  unfold SM_DT_TCR_Experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ bind_congr fun jm ↦ ?_
  unfold tcrWin
  rcases r with ⟨st, qs, tw⟩
  rcases jm with ⟨j, m⟩
  dsimp only
  split <;> rename_i h <;> simp [h]

/-- **Coincidence (program level).** On a classical adversary, the wrapper experiment is VCVio's
experiment run over the general interface. -/
theorem SM_DT_TCR_ExperimentG_ofClassical {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_ExperimentG ds (SM_DT_TCR_AdversaryG.ofClassical ds adv) =
      liftR ds (SM_DT_TCR_Experiment adv) := by
  rw [SM_DT_TCR_Experiment_eq]
  simp only [SM_DT_TCR_ExperimentG, SM_DT_TCR_AdversaryG.ofClassical, runG_embed, liftR_bind,
    liftR_pure]

/-- **Coincidence.** On classical adversaries the wrapper game has VCVio's advantage. -/
theorem SM_DT_TCR_AdvantageG_ofClassical {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_Adversary prob) :
    SM_DT_TCR_AdvantageG ds (SM_DT_TCR_AdversaryG.ofClassical ds adv) =
      SM_DT_TCR_Advantage adv := by
  rw [SM_DT_TCR_AdvantageG, SM_DT_TCR_ExperimentG_ofClassical, prG_liftR]
  rfl

theorem SM_DT_TCR_AdvantageG_le_one {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_TCR_AdversaryG ds prob) : SM_DT_TCR_AdvantageG ds adv ≤ 1 :=
  prG_le_one ds _

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms SM_DT_TCR_AdvantageG_ofClassical
end Axioms
