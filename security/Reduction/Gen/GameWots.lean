import Reduction.Gen.GameTcr

/-!
# Wrapper games: SM-UD and SM-PRE with adversaries over a general sampling spec

VCVio's `SM_DT_UD_Experiment` and `SM_DT_PRE_Experiment` with both phases of the adversary over
`ds + unifSpec` instead of `unifSpec`.  The games themselves (seed generation, challenge and
collection oracles, final check) are VCVio's, run over the general interface by `liftR` / `runG`.

* `SM_DT_UD_AdversaryG`, `SM_DT_UD_ExperimentG` (per world), `SM_DT_UD_RealSuccessG`,
  `SM_DT_UD_IdealSuccessG`, `SM_DT_UD_AdvantageG` (`ENNReal.absDiff` of the two);
* `SM_DT_PRE_AdversaryG`, `SM_DT_PRE_ExperimentG`, `SM_DT_PRE_AdvantageG`;
* `.ofClassical` and the coincidence theorems `SM_DT_UD_RealSuccessG_ofClassical`,
  `SM_DT_UD_IdealSuccessG_ofClassical`, `SM_DT_UD_AdvantageG_ofClassical`,
  `SM_DT_PRE_AdvantageG_ofClassical`;
* `≤ 1` lemmas and non-vacuity through `ofClassical` (SM-UD, SM-PRE, and the tight SM-TCR
  instances of `Reduction/TightCaps.lean`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {ι PkSeed Tweak M M' Y : Type}

/-! ## SM-UD -/

/-- An SM-UD adversary whose two phases may sample from `ds` as well as uniformly. -/
structure SM_DT_UD_AdversaryG (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) where
  /-- Private state carried from `pick` to `distinguish`. -/
  State : Type
  /-- Phase 1: challenge and collection oracles, no seed. -/
  pick : OracleComp
    ((ds + unifSpec) + (SM_DT_UD_challengeSpec Tweak Y + collectionSpec prob.thColl)) State
  /-- Phase 2: the seed, no oracle. -/
  distinguish : State → PkSeed → OracleComp (gSpec ds) Bool

section UD

variable [DecidableEq Tweak]

/-- The SM-UD experiment in one world, for adversaries over the general sampling interface. -/
noncomputable def SM_DT_UD_ExperimentG (world : SM_DT_UD_World)
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_AdversaryG ds prob) :
    OracleComp (gSpec ds) Bool :=
  liftR ds prob.th.seedGen >>= fun pk ↦
    runG ds (SM_DT_UD_oracles world prob pk) adv.pick ([], []) >>= fun r ↦
      adv.distinguish r.1 pk

/-- Success probability in the real world. -/
noncomputable def SM_DT_UD_RealSuccessG {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_AdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (SM_DT_UD_ExperimentG ds .real adv)

/-- Success probability in the ideal world. -/
noncomputable def SM_DT_UD_IdealSuccessG {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_AdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (SM_DT_UD_ExperimentG ds .ideal adv)

/-- The SM-UD advantage of an adversary over the general sampling interface. -/
noncomputable def SM_DT_UD_AdvantageG {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_AdversaryG ds prob) : ℝ≥0∞ :=
  ENNReal.absDiff (SM_DT_UD_RealSuccessG ds adv) (SM_DT_UD_IdealSuccessG ds adv)

/-- A classical adversary as an adversary over the general interface. -/
def SM_DT_UD_AdversaryG.ofClassical {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_Adversary prob) : SM_DT_UD_AdversaryG ds prob where
  State := adv.State
  pick := embed ds adv.pick
  distinguish st pk := liftR ds (adv.distinguish st pk)

/-- VCVio's experiment in the shape of the wrapper experiment. -/
theorem SM_DT_UD_Experiment_eq (world : SM_DT_UD_World)
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_Experiment world adv =
      prob.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_UD_oracles world prob pk) adv.pick).run ([], []) >>= fun r ↦
          adv.distinguish r.1 pk := rfl

/-- **Coincidence (program level).** -/
theorem SM_DT_UD_ExperimentG_ofClassical (world : SM_DT_UD_World)
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_ExperimentG ds world (SM_DT_UD_AdversaryG.ofClassical ds adv) =
      liftR ds (SM_DT_UD_Experiment world adv) := by
  rw [SM_DT_UD_Experiment_eq]
  simp only [SM_DT_UD_ExperimentG, SM_DT_UD_AdversaryG.ofClassical, runG_embed, liftR_bind]

/-- **Coincidence, real world.** -/
theorem SM_DT_UD_RealSuccessG_ofClassical {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_RealSuccessG ds (SM_DT_UD_AdversaryG.ofClassical ds adv) =
      SM_DT_UD_RealSuccess adv := by
  rw [SM_DT_UD_RealSuccessG, SM_DT_UD_ExperimentG_ofClassical, prG_liftR]
  rfl

/-- **Coincidence, ideal world.** -/
theorem SM_DT_UD_IdealSuccessG_ofClassical {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_IdealSuccessG ds (SM_DT_UD_AdversaryG.ofClassical ds adv) =
      SM_DT_UD_IdealSuccess adv := by
  rw [SM_DT_UD_IdealSuccessG, SM_DT_UD_ExperimentG_ofClassical, prG_liftR]
  rfl

/-- **Coincidence.** On classical adversaries the wrapper game has VCVio's advantage. -/
theorem SM_DT_UD_AdvantageG_ofClassical {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_AdvantageG ds (SM_DT_UD_AdversaryG.ofClassical ds adv) =
      SM_DT_UD_Advantage adv := by
  rw [SM_DT_UD_AdvantageG, SM_DT_UD_RealSuccessG_ofClassical, SM_DT_UD_IdealSuccessG_ofClassical]
  rfl

theorem SM_DT_UD_RealSuccessG_le_one {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_AdversaryG ds prob) : SM_DT_UD_RealSuccessG ds adv ≤ 1 :=
  prG_le_one ds _

theorem SM_DT_UD_IdealSuccessG_le_one {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_AdversaryG ds prob) : SM_DT_UD_IdealSuccessG ds adv ≤ 1 :=
  prG_le_one ds _

theorem SM_DT_UD_AdvantageG_le_one {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_UD_AdversaryG ds prob) : SM_DT_UD_AdvantageG ds adv ≤ 1 := by
  unfold SM_DT_UD_AdvantageG ENNReal.absDiff
  rcases le_total (SM_DT_UD_RealSuccessG ds adv) (SM_DT_UD_IdealSuccessG ds adv) with h | h
  · rw [tsub_eq_zero_of_le h, zero_add]
    exact tsub_le_self.trans (SM_DT_UD_IdealSuccessG_le_one ds adv)
  · rw [tsub_eq_zero_of_le h, add_zero]
    exact tsub_le_self.trans (SM_DT_UD_RealSuccessG_le_one ds adv)

end UD

/-! ## SM-PRE -/

/-- An SM-PRE adversary whose two phases may sample from `ds` as well as uniformly. -/
structure SM_DT_PRE_AdversaryG (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) where
  /-- Private state carried from `choose` to `invert`. -/
  State : Type
  /-- Phase 1: challenge and collection oracles, no seed. -/
  choose : OracleComp
    ((ds + unifSpec) + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.thColl)) State
  /-- Phase 2: the seed, no oracle. -/
  invert : State → PkSeed → OracleComp (gSpec ds) (ℕ × M')

section PRE

variable [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']

/-- The final check of the SM-PRE game. -/
def preWin (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed)
    (qsChal : List (Tweak × M')) (jm : ℕ × M') : Bool :=
  match qsChal[jm.1]? with
  | none => false
  | some (t, x) => decide (prob.th.eval pk t (prob.emb jm.2) = prob.th.eval pk t (prob.emb x))

/-- The SM-PRE experiment for adversaries over the general sampling interface. -/
noncomputable def SM_DT_PRE_ExperimentG {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_AdversaryG ds prob) : OracleComp (gSpec ds) Bool :=
  liftR ds prob.th.seedGen >>= fun pk ↦
    runG ds (SM_DT_PRE_oracles prob pk) adv.choose ([], []) >>= fun r ↦
      adv.invert r.1 pk >>= fun jm ↦ pure (preWin prob pk r.2.1 jm)

/-- The SM-PRE advantage of an adversary over the general sampling interface. -/
noncomputable def SM_DT_PRE_AdvantageG {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_AdversaryG ds prob) : ℝ≥0∞ :=
  prG ds (SM_DT_PRE_ExperimentG ds adv)

/-- A classical adversary as an adversary over the general interface. -/
def SM_DT_PRE_AdversaryG.ofClassical {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) : SM_DT_PRE_AdversaryG ds prob where
  State := adv.State
  choose := embed ds adv.choose
  invert st pk := liftR ds (adv.invert st pk)

/-- VCVio's experiment in the shape of the wrapper experiment. -/
theorem SM_DT_PRE_Experiment_eq {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_Experiment adv =
      prob.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_PRE_oracles prob pk) adv.choose).run ([], []) >>= fun r ↦
          adv.invert r.1 pk >>= fun jm ↦ pure (preWin prob pk r.2.1 jm) := by
  unfold SM_DT_PRE_Experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ bind_congr fun jm ↦ ?_
  unfold preWin
  rcases r with ⟨st, qs, tw⟩
  rcases jm with ⟨j, m⟩
  dsimp only
  split <;> rename_i h <;> simp [h]

/-- **Coincidence (program level).** -/
theorem SM_DT_PRE_ExperimentG_ofClassical {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_ExperimentG ds (SM_DT_PRE_AdversaryG.ofClassical ds adv) =
      liftR ds (SM_DT_PRE_Experiment adv) := by
  rw [SM_DT_PRE_Experiment_eq]
  simp only [SM_DT_PRE_ExperimentG, SM_DT_PRE_AdversaryG.ofClassical, runG_embed, liftR_bind,
    liftR_pure]

/-- **Coincidence.** On classical adversaries the wrapper game has VCVio's advantage. -/
theorem SM_DT_PRE_AdvantageG_ofClassical {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_Adversary prob) :
    SM_DT_PRE_AdvantageG ds (SM_DT_PRE_AdversaryG.ofClassical ds adv) =
      SM_DT_PRE_Advantage adv := by
  rw [SM_DT_PRE_AdvantageG, SM_DT_PRE_ExperimentG_ofClassical, prG_liftR]
  rfl

theorem SM_DT_PRE_AdvantageG_le_one {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : SM_DT_PRE_AdversaryG ds prob) : SM_DT_PRE_AdvantageG ds adv ≤ 1 :=
  prG_le_one ds _

end PRE

/-! ## Non-vacuity (through `ofClassical`) -/

section NonVacuity

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y]

/-- In the wrapper game a constant SM-UD distinguisher has advantage `0`. -/
theorem ud_const_advG_zero (pkSeedDist : ProbComp prims.PkSeed) (b : Bool) :
    SM_DT_UD_AdvantageG ds (SM_DT_UD_AdversaryG.ofClassical ds
      (⟨Unit, pure (), fun _ _ ↦ pure b⟩ :
        SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))) = 0 := by
  rw [SM_DT_UD_AdvantageG_ofClassical]
  exact ud_const_adv_zero pkSeedDist b

/-- SM-UD can be won in the wrapper game (if `F(·, t, ·)` is constant). -/
theorem udTester_advG [Fintype prims.Y] (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < wotsChainTargets vp) (t : prims.AdrsKey) (c : prims.Y)
    (hconst : ∀ pk x, prims.Thash pk t [x] = c) :
    SM_DT_UD_AdvantageG ds (SM_DT_UD_AdversaryG.ofClassical ds
      (udTester (vp := vp) pkSeedDist t c)) = 1 - (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
  rw [SM_DT_UD_AdvantageG_ofClassical]
  exact udTester_adv pkSeedDist h0 t c hconst

/-- On the toy bundle the wrapper SM-UD game is won with advantage `1/2`. -/
theorem toy_udG (vp : ValidatedParams) (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : SM_DT_UD_AdversaryG ds (wotsUdProblem vp (toyPrims vp.params) pkSeedDist),
      SM_DT_UD_AdvantageG ds B = 2⁻¹ := by
  obtain ⟨B, hB⟩ := toy_ud (vp := vp) pkSeedDist
  exact ⟨_, (SM_DT_UD_AdvantageG_ofClassical ds B).trans hB⟩

/-- SM-PRE can be lost in the wrapper game. -/
theorem pre_trivial_advG_zero (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_PRE_AdvantageG ds (SM_DT_PRE_AdversaryG.ofClassical ds
      (⟨Unit, pure (), fun _ _ ↦ pure (0, default)⟩ :
        SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))) = 0 := by
  rw [SM_DT_PRE_AdvantageG_ofClassical]
  exact pre_trivial_adv_zero pkSeedDist

/-- SM-PRE can be won in the wrapper game. -/
theorem preInverter_advG_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < wotsChainTargets vp)
    (t : prims.AdrsKey) (y₀ : prims.Y)
    (hconst : ∀ pk x, prims.Thash pk t [y₀] = prims.Thash pk t [x]) :
    SM_DT_PRE_AdvantageG ds (SM_DT_PRE_AdversaryG.ofClassical ds
      (preInverter (vp := vp) pkSeedDist t y₀)) = 1 := by
  rw [SM_DT_PRE_AdvantageG_ofClassical]
  exact preInverter_adv_one pkSeedDist h0 t y₀ hconst

/-- On the toy bundle the wrapper SM-PRE game is won with probability `1`. -/
theorem toy_preG (vp : ValidatedParams) (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : SM_DT_PRE_AdversaryG ds (wotsPreProblem vp (toyPrims vp.params) pkSeedDist),
      SM_DT_PRE_AdvantageG ds B = 1 := by
  obtain ⟨B, hB⟩ := toy_pre (vp := vp) pkSeedDist
  exact ⟨_, (SM_DT_PRE_AdvantageG_ofClassical ds B).trans hB⟩

/-! ### The tight SM-TCR instances -/

/-- The tight arity-`n` wrapper game can be lost. -/
theorem thashArityT_trivial_advG_zero (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) :
    SM_DT_TCR_AdvantageG ds (SM_DT_TCR_AdversaryG.ofClassical ds
      (⟨Unit, pure (), fun _ _ ↦ pure (0, arityDefault prims n)⟩ :
        SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n))) = 0 := by
  rw [SM_DT_TCR_AdvantageG_ofClassical]
  exact thashArityT_trivial_adv_zero pkSeedDist n

/-- The tight arity-`n` wrapper game can be won. -/
theorem thashArityColliderT_advG_one (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ)
    (h0 : 0 < arityTargets vp n) (t : prims.AdrsKey) (x y : {xs : List prims.Y // xs.length = n})
    (hne : y ≠ x) (hcol : ∀ pk, prims.Thash pk t y.1 = prims.Thash pk t x.1) :
    SM_DT_TCR_AdvantageG ds (SM_DT_TCR_AdversaryG.ofClassical ds
      (thashArityColliderT (vp := vp) pkSeedDist n t x y)) = 1 := by
  rw [SM_DT_TCR_AdvantageG_ofClassical]
  exact thashArityColliderT_adv_one pkSeedDist n h0 t x y hne hcol

/-- The tight WOTS+ SM-TCR wrapper game can be lost. -/
theorem wotsTcrT_trivial_advG_zero (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_TCR_AdvantageG ds (SM_DT_TCR_AdversaryG.ofClassical ds
      (⟨Unit, pure (), fun _ _ ↦ pure (0, default)⟩ :
        SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist))) = 0 := by
  rw [SM_DT_TCR_AdvantageG_ofClassical]
  exact wotsTcrT_trivial_adv_zero pkSeedDist

/-- The tight WOTS+ SM-TCR wrapper game can be won. -/
theorem wotsTcrColliderT_advG_one (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < wotsStepTargetsT vp) (t : prims.AdrsKey) (x y : prims.Y) (hne : y ≠ x)
    (hcol : ∀ pk, prims.Thash pk t [y] = prims.Thash pk t [x]) :
    SM_DT_TCR_AdvantageG ds (SM_DT_TCR_AdversaryG.ofClassical ds
      (wotsTcrColliderT (vp := vp) pkSeedDist t x y)) = 1 := by
  rw [SM_DT_TCR_AdvantageG_ofClassical]
  exact wotsTcrColliderT_adv_one pkSeedDist h0 t x y hne hcol

end NonVacuity

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms SM_DT_UD_RealSuccessG_ofClassical
#print axioms SM_DT_UD_IdealSuccessG_ofClassical
#print axioms SM_DT_UD_AdvantageG_ofClassical
#print axioms SM_DT_PRE_AdvantageG_ofClassical
#print axioms SM_DT_UD_AdvantageG_le_one
#print axioms udTester_advG
#print axioms preInverter_advG_one
#print axioms thashArityColliderT_advG_one
#print axioms wotsTcrColliderT_advG_one
end Axioms
