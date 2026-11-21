import Reduction.Gen.Sem
import Reduction.NonVacuity

/-!
# Wrapper game: ITSR with adversaries over a general sampling spec

VCVio's `KeyedHash.ITSRExperiment` with the adversary's program over
`(ds + unifSpec) + ITSRTargetSpec X K` instead of `unifSpec + ITSRTargetSpec X K`.  The game
(target oracle `ITSROracles`, final relation `Wins`) is VCVio's, run over the general interface by
`runG`.

* `ITSRAdversaryG`, `ITSRExperimentG`, `ITSRAdvantageG`;
* `ITSRAdversaryG.ofClassical`, `ITSRAdvantageG_ofClassical`: on classical adversaries the wrapper
  game has VCVio's advantage;
* non-vacuity: `ITSRAdvantageG_le_one`, `itsr_trivial_advG_zero`, `itsrReplayer_advG_one`
  (the classical lemmas of `Reduction/NonVacuity.lean`, through `ofClassical`).
-/

open OracleComp OracleSpec ENNReal KeyedHash SLHDSA SLHDSA.Security

namespace Reduction.Gen

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {K X Y Index : Type}

/-- An ITSR adversary that may sample from `ds` as well as uniformly. -/
structure ITSRAdversaryG (prob : ITSRProblem K X Y Index) where
  /-- The adversary's computation: general sampling and the target oracle. -/
  main : OracleComp ((ds + unifSpec) + ITSRTargetSpec X K) (K × X)

/-- A classical adversary as an adversary over the general interface. -/
def ITSRAdversaryG.ofClassical {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) :
    ITSRAdversaryG ds prob where
  main := embed ds adv.main

variable [DecidableEq K] [DecidableEq X] [DecidableEq Index]

/-- The ITSR experiment for adversaries over the general sampling interface. -/
noncomputable def ITSRExperimentG {prob : ITSRProblem K X Y Index}
    (adv : ITSRAdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  runG ds (ITSROracles prob) adv.main [] >>= fun r ↦ pure (decide (prob.Wins r.2 r.1))

/-- The ITSR success probability of an adversary over the general sampling interface. -/
noncomputable def ITSRAdvantageG {prob : ITSRProblem K X Y Index}
    (adv : ITSRAdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (ITSRExperimentG ds adv)

/-- VCVio's experiment in the shape of the wrapper experiment. -/
theorem ITSRExperiment_eq {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) :
    ITSRExperiment adv =
      (simulateQ (ITSROracles prob) adv.main).run [] >>= fun r ↦
        pure (decide (prob.Wins r.2 r.1)) := rfl

/-- **Coincidence (program level).** -/
theorem ITSRExperimentG_ofClassical {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) :
    ITSRExperimentG ds (ITSRAdversaryG.ofClassical ds adv) = liftR ds (ITSRExperiment adv) := by
  rw [ITSRExperiment_eq]
  simp only [ITSRExperimentG, ITSRAdversaryG.ofClassical, runG_embed, liftR_bind, liftR_pure]

/-- **Coincidence.** On classical adversaries the wrapper game has VCVio's advantage. -/
theorem ITSRAdvantageG_ofClassical {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) :
    ITSRAdvantageG ds (ITSRAdversaryG.ofClassical ds adv) = ITSRAdvantage adv := by
  rw [ITSRAdvantageG, ITSRExperimentG_ofClassical, prG_liftR,
    ITSRAdvantage_eq_evalDist_experiment]
  rfl

theorem ITSRAdvantageG_le_one {prob : ITSRProblem K X Y Index} (adv : ITSRAdversaryG ds prob) :
    ITSRAdvantageG ds adv ≤ 1 :=
  prG_le_one ds _

/-! ## Non-vacuity (through `ofClassical`) -/

section NonVacuity

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y]

/-- ITSR can be lost in the wrapper game. -/
theorem itsr_trivial_advG_zero (c : prims.Y × prims.PkSeed × prims.Y × List Byte) :
    ITSRAdvantageG ds (ITSRAdversaryG.ofClassical ds
      (⟨pure c⟩ : ITSRAdversary (itsrProblem vp prims))) = 0 := by
  rw [ITSRAdvantageG_ofClassical]
  exact itsr_trivial_adv_zero c

/-- ITSR can be won in the wrapper game (when `H_msg` has a randomizer-independent collision). -/
theorem itsrReplayer_advG_one (pk : prims.PkSeed) (root : prims.Y) (m m' : List Byte)
    (hne : m' ≠ m) (hcol : ∀ R, prims.Hmsg R pk root m' = prims.Hmsg R pk root m) :
    ITSRAdvantageG ds (ITSRAdversaryG.ofClassical ds (itsrReplayer (vp := vp) pk root m m')) =
      1 := by
  rw [ITSRAdvantageG_ofClassical]
  exact itsrReplayer_adv_one pk root m m' hne hcol

end NonVacuity

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms ITSRAdvantageG_ofClassical
#print axioms itsr_trivial_advG_zero
#print axioms itsrReplayer_advG_one
end Axioms
