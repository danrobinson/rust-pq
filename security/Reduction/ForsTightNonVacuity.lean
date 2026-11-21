import Reduction.ForsTightFinal

/-!
# Non-vacuity of the two games introduced by the tight FORS term

`forsDsprProblem` (SM-DT-DSPR on `F`) and `forsTcrProblem` (source-final-validity SM-DT-TCR on
`F`) are new on the right-hand side of `slhdsa_euf_cma_fors_tight`.  Each can be lost and, for a
degenerate `F`, won with advantage `1`; the degeneracy conditions are met by toy bundles
(`toyPrims` of `Reduction/NonVacuity.lean` for TCR; `toyInjPrims` below, where `F` is the
identity, for DSPR).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MeasureTheory

namespace Reduction

open TweakableHash

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-! ## SM-DT-TCR on `F` (final-validity form) -/

/-- The FORS SM-TCR game can be lost: the adversary that asks for no target has advantage `0`. -/
theorem forsTcr_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_TCR_SourceFinalValidity.advantage (prob := forsTcrProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [SM_DT_TCR_SourceFinalValidity.experiment, SourceFinalValidity.State.initial] at hx
  exact hx.2

/-- The FORS SM-TCR adversary that commits to the target `(t, x)` and answers `y`. -/
def forsTcrCollider (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (x y : prims.Y) :
    SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp prims pkSeedDist) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec prims.AdrsKey prims.Y prims.Y +
      SourceFinalValidity.collectionSpec (forsTcrProblem vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl (t, x)))
    pure ()
  forge := fun _ _ => pure (0, y)

/-- The FORS SM-TCR game can be won: if `F` has a seed-independent collision `x ≠ y` at some
tweak, `forsTcrCollider` wins with probability `1`. -/
theorem forsTcrCollider_adv_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < openPreTargets vp)
    (t : prims.AdrsKey) (x y : prims.Y) (hne : y ≠ x)
    (hcol : ∀ pk, prims.Thash pk t [y] = prims.Thash pk t [x]) :
    SM_DT_TCR_SourceFinalValidity.advantage (forsTcrCollider (vp := vp) pkSeedDist t x y) = 1 := by
  apply prTrue_eq_one_of_support
  intro b hb
  have hn : (forsTcrProblem vp prims pkSeedDist).numTargets = openPreTargets vp := rfl
  simp [SM_DT_TCR_SourceFinalValidity.experiment, forsTcrCollider,
    SM_DT_TCR_SourceFinalValidity.oracles, SM_DT_TCR_SourceFinalValidity.challengeOracle,
    SourceFinalValidity.State.initial, SourceFinalValidity.State.recordTarget,
    TweakFresh, TweakReserved, hn, h0] at hb
  obtain ⟨pk, -, rfl⟩ := hb
  have h : (forsTcrProblem vp prims pkSeedDist).th.eval pk t y =
      (forsTcrProblem vp prims pkSeedDist).th.eval pk t x := hcol pk
  simp [hne, h]

/-! ## SM-DT-DSPR on `F` -/

section Dspr

variable [Fintype prims.Y]

/-- The FORS SM-DSPR game can be lost: the adversary that asks for no target has advantage `0`. -/
theorem forsDspr_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_DSPR_SourceFinalValidity.advantage (prob := forsDsprProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure (0, false)⟩ = 0 := by
  unfold SM_DT_DSPR_SourceFinalValidity.advantage SM_DT_DSPR_SourceFinalValidity.Success
  rw [prTrue_eq_zero_of_support, zero_tsub]
  intro x hx
  simp [SM_DT_DSPR_SourceFinalValidity.experiment, SourceFinalValidity.State.initial] at hx
  exact hx.2

/-- The FORS SM-DSPR adversary that commits to the target `(t, x)` and guesses `b`. -/
def forsDsprGuesser (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (x : prims.Y)
    (b : Bool) :
    SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp prims pkSeedDist) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec prims.AdrsKey prims.Y prims.Y +
      SourceFinalValidity.collectionSpec (forsDsprProblem vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl (t, x)))
    pure ()
  guess := fun _ _ => pure (0, b)

/-- The FORS SM-DSPR game can be won: if `F(pk, t, ·)` never maps another input to the image of
`x`, the adversary that targets `(t, x)` and guesses "no second preimage" has advantage `1`
(`Pr[DSPR] = 1`, `Pr[SPprob] = 0`). -/
theorem forsDsprGuesser_adv_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < openPreTargets vp)
    (t : prims.AdrsKey) (x : prims.Y)
    (hinj : ∀ pk y, prims.Thash pk t [x] = prims.Thash pk t [y] → x = y) :
    SM_DT_DSPR_SourceFinalValidity.advantage
      (forsDsprGuesser (vp := vp) pkSeedDist t x false) = 1 := by
  have hn : (forsDsprProblem vp prims pkSeedDist).numTargets = openPreTargets vp := rfl
  have hspe : ∀ pk, ¬ SecondPreimageExists (forsDsprProblem vp prims pkSeedDist).th pk t x := by
    rintro pk ⟨y, hne, heq⟩
    exact hne (hinj pk y heq)
  unfold SM_DT_DSPR_SourceFinalValidity.advantage SM_DT_DSPR_SourceFinalValidity.Success
    SM_DT_DSPR_SourceFinalValidity.SPProbability
  have h1 : 𝒟[SM_DT_DSPR_SourceFinalValidity.experiment
      (forsDsprGuesser (vp := vp) pkSeedDist t x false)] {true} = 1 := by
    apply prTrue_eq_one_of_support
    intro b hb
    simp [SM_DT_DSPR_SourceFinalValidity.experiment, forsDsprGuesser,
      SM_DT_DSPR_SourceFinalValidity.oracles, SM_DT_DSPR_SourceFinalValidity.challengeOracle,
      SourceFinalValidity.State.initial, SourceFinalValidity.State.recordTarget,
      TweakFresh, TweakReserved, hn, h0] at hb
    obtain ⟨pk, -, h⟩ := hb
    have hd : decide (SecondPreimageExists (forsDsprProblem vp prims pkSeedDist).th pk t x) =
        false := decide_eq_false (hspe pk)
    rw [hd] at h
    cases b with
    | true => rfl
    | false => exact absurd h (by decide)
  have h2 : 𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment
      (forsDsprGuesser (vp := vp) pkSeedDist t x false)] {true} = 0 := by
    apply prTrue_eq_zero_of_support
    intro b hb
    simp [SM_DT_DSPR_SourceFinalValidity.spExperiment, forsDsprGuesser,
      SM_DT_DSPR_SourceFinalValidity.oracles, SM_DT_DSPR_SourceFinalValidity.challengeOracle,
      SourceFinalValidity.State.initial, SourceFinalValidity.State.recordTarget,
      TweakFresh, TweakReserved, hn, h0] at hb
    obtain ⟨pk, -, rfl⟩ := hb
    simp [hspe pk]
  rw [h1, h2, tsub_zero]

/-- The baseline subtraction is effective: guessing "a second preimage exists" for a target that
always has one gives `Pr[DSPR] = Pr[SPprob] = 1`, hence advantage `0` (not `1`). -/
theorem forsDsprGuesser_adv_zero_of_collision (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < openPreTargets vp) (t : prims.AdrsKey) (x y : prims.Y) (hne : x ≠ y)
    (hcol : ∀ pk, prims.Thash pk t [x] = prims.Thash pk t [y]) :
    SM_DT_DSPR_SourceFinalValidity.advantage
      (forsDsprGuesser (vp := vp) pkSeedDist t x true) = 0 := by
  have hn : (forsDsprProblem vp prims pkSeedDist).numTargets = openPreTargets vp := rfl
  have hspe : ∀ pk, SecondPreimageExists (forsDsprProblem vp prims pkSeedDist).th pk t x :=
    fun pk => ⟨y, hne, hcol pk⟩
  unfold SM_DT_DSPR_SourceFinalValidity.advantage SM_DT_DSPR_SourceFinalValidity.Success
    SM_DT_DSPR_SourceFinalValidity.SPProbability
  have h2 : 𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment
      (forsDsprGuesser (vp := vp) pkSeedDist t x true)] {true} = 1 := by
    apply prTrue_eq_one_of_support
    intro b hb
    simp [SM_DT_DSPR_SourceFinalValidity.spExperiment, forsDsprGuesser,
      SM_DT_DSPR_SourceFinalValidity.oracles, SM_DT_DSPR_SourceFinalValidity.challengeOracle,
      SourceFinalValidity.State.initial, SourceFinalValidity.State.recordTarget,
      TweakFresh, TweakReserved, hn, h0] at hb
    obtain ⟨pk, -, rfl⟩ := hb
    simp [hspe pk]
  rw [h2]
  exact tsub_eq_zero_of_le (prob_le_one)

end Dspr

/-! ## Toy bundles -/

section Toy

variable (vp : ValidatedParams)

/-- On the constant toy bundle the FORS SM-TCR game is won with probability `1`. -/
theorem toy_forsTcr (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : SM_DT_TCR_SourceFinalValidity.Adversary
        (forsTcrProblem vp (toyPrims vp.params) pkSeedDist),
      SM_DT_TCR_SourceFinalValidity.advantage B = 1 :=
  ⟨_, forsTcrCollider_adv_one (prims := toyPrims vp.params) pkSeedDist (openPreTargets_pos vp)
    (default : Adrs) false true (show (true : Bool) ≠ false by decide) fun _ => rfl⟩

/-- On the constant toy bundle (every input has a second preimage) guessing `true` gains
nothing. -/
theorem toy_forsDspr_zero (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    SM_DT_DSPR_SourceFinalValidity.advantage
      (forsDsprGuesser (vp := vp) (prims := toyPrims vp.params) pkSeedDist
        (default : Adrs) false true) = 0 :=
  forsDsprGuesser_adv_zero_of_collision (prims := toyPrims vp.params) pkSeedDist
    (openPreTargets_pos vp) (default : Adrs) false true (show (false : Bool) ≠ true by decide)
    fun _ => rfl

/-- A toy bundle whose `F` is injective: one-bit nodes, `Thash` returns the first input. -/
def toyInjPrims (p : Params) : Primitives p where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bool
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ _ => false
  PRFmsg := fun _ _ _ => false
  yToBytes := fun b => Vector.replicate p.n (if b then 1 else 0)
  Thash := fun _ _ xs => xs.headD false
  Hmsg := fun _ _ _ _ => Vector.replicate p.m 0

instance : SampleableType (toyInjPrims vp.params).Y := inferInstanceAs (SampleableType Bool)
instance : SampleableType (toyInjPrims vp.params).SkSeed := inferInstanceAs (SampleableType Unit)
instance : SampleableType (toyInjPrims vp.params).SkPrf := inferInstanceAs (SampleableType Unit)
instance : DecidableEq (toyInjPrims vp.params).Y := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq (toyInjPrims vp.params).PkSeed := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq (toyInjPrims vp.params).AdrsKey := inferInstanceAs (DecidableEq Adrs)
instance : Inhabited (toyInjPrims vp.params).Y := inferInstanceAs (Inhabited Bool)
instance : Fintype (toyInjPrims vp.params).Y := inferInstanceAs (Fintype Bool)

/-- On the injective toy bundle the FORS SM-DSPR game is won with advantage `1`. -/
theorem toyInj_forsDspr (pkSeedDist : ProbComp (toyInjPrims vp.params).PkSeed) :
    ∃ B : SM_DT_DSPR_SourceFinalValidity.Adversary
        (forsDsprProblem vp (toyInjPrims vp.params) pkSeedDist),
      SM_DT_DSPR_SourceFinalValidity.advantage B = 1 :=
  ⟨_, forsDsprGuesser_adv_one (prims := toyInjPrims vp.params) pkSeedDist (openPreTargets_pos vp)
    (default : Adrs) false fun _ _ h => h⟩

end Toy

#print axioms forsDsprGuesser_adv_one
#print axioms forsDsprGuesser_adv_zero_of_collision
#print axioms forsTcrCollider_adv_one
#print axioms toyInj_forsDspr
#print axioms toy_forsTcr

end Reduction
