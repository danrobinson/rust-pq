import Reduction.Final

/-!
# Non-vacuity of the games

Each game on the right-hand side of the final bound is a genuine game: it can be **lost** (some
adversary has advantage `0`, so the bound is not `≥ 1` by construction) and it can be **won**
(for a degenerate primitive bundle some explicit adversary has the maximal advantage, so the
assumption "the advantage is small" is a real restriction on `prims`).

| game (final-bound term) | lost | won (degenerate bundle) |
|---|---|---|
| SM-TCR (`tcrProblem`, `wotsTcrProblem`) | `tcr_trivial_adv_zero`, `wotsTcr_trivial_adv_zero` | `tcrCollider_adv_one`, `tcr_winnable`; `wotsTcrCollider_adv_one` |
| SM-PRE (`wotsPreProblem`) | `pre_trivial_adv_zero` | `preInverter_adv_one`, `pre_winnable` |
| ITSR (`itsrProblem`) | `itsr_trivial_adv_zero` | `itsrReplayer_adv_one` |
| SM-DT-OpenPRE (`forsOpenPreProblem`) | `openPre_trivial_adv_zero` | `openPreInverter_adv_one` |
| PRF (`skPrf`, `msgPrf`) | `prf_const_adv_zero`, `prfMsg_const_adv_zero` | `prfTester_adv`, `prfMsgTester_adv` (`= 1 - 1/|Y|`) |
| SM-UD (`wotsUdProblem`) | `ud_const_adv_zero` | `udTester_adv` (`= 1 - 1/|Y|`) |

The "won" statements are about an arbitrary bundle satisfying an explicit degeneracy condition
(a seed-independent collision, a tweak at which `F` is constant, …).  That these conditions are
satisfiable *for every parameter set* is shown by the toy bundle `toyPrims` (all hash functions
constant, `Y = Bool`): section `Toy` instantiates every "won" lemma at it, with the target-count
side conditions discharged (`tcrTargets_pos`, `wotsChainTargets_pos`, `openPreTargets_pos`).
There the search games have advantage exactly `1` and the two distinguishing games exactly `1/2`.

For the two distinguishing games (PRF, SM-UD) the advantage is `|Pr[real] − Pr[ideal]|`; "lost"
means a constant distinguisher has advantage `0`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MeasureTheory

namespace Reduction

/-! ## Probability helpers -/

/-- A Boolean experiment all of whose possible outputs are `false` succeeds with probability `0`. -/
theorem prTrue_eq_zero_of_support (g : ProbComp Bool) (h : ∀ x ∈ support g, x = false) :
    𝒟[g] {true} = 0 :=
  evalDist.apply_eq_zero_of_disjoint_support g (MeasurableSet.of_discrete) (by
    intro x hx; simp [h x hx])

/-- A Boolean experiment all of whose possible outputs are `true` succeeds with probability `1`. -/
theorem prTrue_eq_one_of_support (g : ProbComp Bool) (h : ∀ x ∈ support g, x = true) :
    𝒟[g] {true} = 1 := by
  have h0 : 𝒟[g] {false} = 0 :=
    evalDist.apply_eq_zero_of_disjoint_support g (MeasurableSet.of_discrete) (by
      intro x hx; simp [h x hx])
  have : IsProbabilityMeasure 𝒟[g] := inferInstance
  have hc : ({true} : Set Bool) = {false}ᶜ := by ext b; cases b <;> simp
  rw [hc, MeasureTheory.prob_compl_eq_one_sub (MeasurableSet.of_discrete), h0, tsub_zero]

/-- A uniform sample hits a fixed point with probability `1/|α|`. -/
theorem prTrue_map_decide_uniform {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (c : α) :
    𝒟[(fun a => decide (a = c)) <$> ($ᵗ α : ProbComp α)] {true} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let _ : MeasurableSpace α := ⊤
  rw [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)]
  have : (fun a => decide (a = c)) ⁻¹' {true} = {c} := by ext a; simp
  rw [this, SampleableType.evalDist_uniformSample_singleton]

/-- `|1 − 1/n| = 1 − 1/n` for a nonempty finite type. -/
theorem absDiff_one_inv_card (α : Type) [Fintype α] [Nonempty α] :
    ENNReal.absDiff 1 (Fintype.card α : ℝ≥0∞)⁻¹ = 1 - (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have h : (Fintype.card α : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (by exact_mod_cast Fintype.card_pos)
  simp [ENNReal.absDiff, tsub_eq_zero_of_le h]

/-! ## Target counts are positive -/

theorem wotsInstanceCount_pos (vp : ValidatedParams) : 0 < wotsInstanceCount vp.params := by
  unfold wotsInstanceCount
  have : Nonempty (Fin vp.params.d) := ⟨⟨0, vp.valid.d_pos⟩⟩
  exact Finset.sum_pos (fun i _ => by unfold treesAtLayer; positivity) Finset.univ_nonempty

theorem openPreTargets_pos (vp : ValidatedParams) : 0 < openPreTargets vp := by
  have := vp.valid.k_pos
  unfold openPreTargets targetCount
  positivity

theorem wotsChainTargets_pos (vp : ValidatedParams) : 0 < wotsChainTargets vp :=
  Nat.mul_pos (wotsInstanceCount_pos vp) vp.params.len_pos

theorem tcrTargets_pos (vp : ValidatedParams) : 0 < tcrTargets vp := by
  have := openPreTargets_pos vp
  unfold openPreTargets at this
  unfold tcrTargets
  rw [constructionAddresses_length]
  omega

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-! ## SM-TCR -/

/-- SM-TCR can be lost: the adversary that asks for no target has advantage `0`. -/
theorem tcr_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_TCR_Advantage (prob := tcrProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure (0, [])⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [TweakableHash.SM_DT_TCR_Experiment] at hx
  exact hx.2

/-- The WOTS+ SM-TCR game (last term of the bound) can be lost in the same way. -/
theorem wotsTcr_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_TCR_Advantage (prob := wotsTcrProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [TweakableHash.SM_DT_TCR_Experiment] at hx
  exact hx.2

theorem wotsStepTargets_pos (vp : ValidatedParams) : 0 < wotsStepTargets vp :=
  targetCount_pos vp.params vp.valid .wotsFTcr

/-- The WOTS+ SM-TCR adversary (on `F`) that commits to the target `(t, x)` and answers `y`. -/
def wotsTcrCollider (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (x y : prims.Y) :
    TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
      TweakableHash.collectionSpec (wotsTcrProblem vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl (t, x)))
    pure ()
  forge := fun _ _ => pure (0, y)

/-- SM-TCR on `F` (last term of the bound) can be won: if `F` has a seed-independent collision
`x ≠ y` at some tweak, `wotsTcrCollider` wins with probability `1`.
(`0 < wotsStepTargets vp` always holds: `wotsStepTargets_pos`.) -/
theorem wotsTcrCollider_adv_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < wotsStepTargets vp)
    (t : prims.AdrsKey) (x y : prims.Y) (hne : y ≠ x)
    (hcol : ∀ pk, prims.Thash pk t [y] = prims.Thash pk t [x]) :
    TweakableHash.SM_DT_TCR_Advantage (wotsTcrCollider (vp := vp) pkSeedDist t x y) = 1 := by
  apply prTrue_eq_one_of_support
  intro b hb
  have hrun : ∀ pk, (TweakableHash.SM_DT_TCR_challengeOracle (wotsTcrProblem vp prims pkSeedDist) pk
      (t, x)).run (([], []) : TweakableHash.SM_DT_TCR_State prims.AdrsKey prims.Y) = _ :=
    fun pk => TweakableHash.SM_DT_TCR_challengeOracle_run_of_fresh (by exact h0)
      (by simp [TweakableHash.TweakFresh, TweakableHash.TweakReserved])
  simp [TweakableHash.SM_DT_TCR_Experiment, wotsTcrCollider, TweakableHash.SM_DT_TCR_oracles,
    hrun] at hb
  obtain ⟨pk, -, rfl⟩ := hb
  have h : (wotsTcrProblem vp prims pkSeedDist).th.eval pk t y =
      (wotsTcrProblem vp prims pkSeedDist).th.eval pk t x := hcol pk
  simp [hne, h]

/-- The SM-TCR adversary that commits to the target `(t, xs)` and answers `ys`. -/
def tcrCollider (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (xs ys : List prims.Y) :
    TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey (List prims.Y) prims.Y +
      TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl (t, xs)))
    pure ()
  forge := fun _ _ => pure (0, ys)

/-- SM-TCR can be won: if `Thash` has a seed-independent collision `xs ≠ ys` at some tweak and at
least one target is allowed, `tcrCollider` wins with probability `1`. -/
theorem tcrCollider_adv_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < tcrTargets vp)
    (t : prims.AdrsKey) (xs ys : List prims.Y) (hne : ys ≠ xs)
    (hcol : ∀ pk, prims.Thash pk t ys = prims.Thash pk t xs) :
    TweakableHash.SM_DT_TCR_Advantage (tcrCollider (vp := vp) pkSeedDist t xs ys) = 1 := by
  apply prTrue_eq_one_of_support
  intro x hx
  have hrun : ∀ pk, (TweakableHash.SM_DT_TCR_challengeOracle (tcrProblem vp prims pkSeedDist) pk
      (t, xs)).run (([], []) : TweakableHash.SM_DT_TCR_State prims.AdrsKey (List prims.Y)) = _ :=
    fun pk => TweakableHash.SM_DT_TCR_challengeOracle_run_of_fresh (by exact h0)
      (by simp [TweakableHash.TweakFresh, TweakableHash.TweakReserved])
  simp [TweakableHash.SM_DT_TCR_Experiment, tcrCollider, TweakableHash.SM_DT_TCR_oracles, hrun] at hx
  obtain ⟨pk, -, rfl⟩ := hx
  have h : (tcrProblem vp prims pkSeedDist).th.eval pk t ys =
      (tcrProblem vp prims pkSeedDist).th.eval pk t xs := hcol pk
  simp [hne, h]

/-- SM-TCR can be won: if `Thash` ignores its input and at least one target is allowed, some
adversary has advantage `1`.  (`0 < tcrTargets vp` always holds: `tcrTargets_pos`.) -/
theorem tcr_winnable (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < tcrTargets vp)
    (hconst : ∀ pk t xs ys, prims.Thash pk t xs = prims.Thash pk t ys) :
    ∃ B : TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist),
      TweakableHash.SM_DT_TCR_Advantage B = 1 :=
  ⟨_, tcrCollider_adv_one pkSeedDist h0 (prims.adrsToKey default) [] [default] (by simp)
    fun pk => hconst pk _ _ _⟩

/-! ## SM-PRE -/

/-- SM-PRE can be lost: the adversary that asks for no target has advantage `0`. -/
theorem pre_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_PRE_Advantage (prob := wotsPreProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [TweakableHash.SM_DT_PRE_Experiment] at hx
  exact hx.2

/-- The SM-PRE adversary that asks for one target at tweak `t` and answers `y₀`. -/
def preInverter (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (y₀ : prims.Y) :
    TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (TweakableHash.SM_DT_PRE_challengeSpec prims.AdrsKey prims.Y +
      TweakableHash.collectionSpec (wotsPreProblem vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl t))
    pure ()
  invert := fun _ _ => pure (0, y₀)

/-- SM-PRE can be won: if `F(·, t, ·)` takes the value `F(pk, t, y₀)` everywhere, `preInverter`
wins with probability `1`. -/
theorem preInverter_adv_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < wotsChainTargets vp)
    (t : prims.AdrsKey) (y₀ : prims.Y)
    (hconst : ∀ pk x, prims.Thash pk t [y₀] = prims.Thash pk t [x]) :
    TweakableHash.SM_DT_PRE_Advantage (preInverter (vp := vp) pkSeedDist t y₀) = 1 := by
  apply prTrue_eq_one_of_support
  intro x hx
  have hrun : ∀ pk, (TweakableHash.SM_DT_PRE_challengeOracle (wotsPreProblem vp prims pkSeedDist) pk
      t).run (([], []) : TweakableHash.SM_DT_PRE_State prims.AdrsKey prims.Y) = _ :=
    fun pk => TweakableHash.SM_DT_PRE_challengeOracle_run_of_fresh (by exact h0)
      (by simp [TweakableHash.TweakFresh, TweakableHash.TweakReserved])
  simp [TweakableHash.SM_DT_PRE_Experiment, preInverter, TweakableHash.SM_DT_PRE_oracles, hrun] at hx
  obtain ⟨pk, -, y, rfl⟩ := hx
  exact decide_eq_true (hconst pk y)

/-- SM-PRE can be won under the same degeneracy as SM-TCR.
(`0 < wotsChainTargets vp` always holds: `wotsChainTargets_pos`.) -/
theorem pre_winnable (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < wotsChainTargets vp)
    (hconst : ∀ pk t xs ys, prims.Thash pk t xs = prims.Thash pk t ys) :
    ∃ B : TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist),
      TweakableHash.SM_DT_PRE_Advantage B = 1 :=
  ⟨_, preInverter_adv_one pkSeedDist h0 (prims.adrsToKey default) default
    fun pk _ => hconst pk _ _ _⟩

/-! ## ITSR -/

/-- ITSR can be lost: an adversary that makes no target query cannot be covered, because every
digest opens `k > 0` FORS leaves. -/
theorem itsr_trivial_adv_zero (c : prims.Y × prims.PkSeed × prims.Y × List Byte) :
    KeyedHash.ITSRAdvantage (prob := itsrProblem vp prims) ⟨pure c⟩ = 0 := by
  rw [KeyedHash.ITSRAdvantage_eq_evalDist_experiment]
  apply prTrue_eq_zero_of_support
  intro x hx
  simp only [KeyedHash.ITSRExperiment, KeyedHash.ITSRAdversary.run, simulateQ_pure,
    StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hx
  rw [hx, decide_eq_false_iff_not]
  intro h
  have hmem : ∃ i, i ∈ (itsrProblem vp prims).indexSet c :=
    ⟨_, List.mem_map.2 ⟨0, List.mem_range.2 vp.valid.k_pos, rfl⟩⟩
  obtain ⟨i, hi⟩ := hmem
  simpa [KeyedHash.ITSRProblem.targetIndexSet] using h.2 i hi

/-- The ITSR adversary that asks for a target on `(pk, root, m)` and replays the returned
randomizer on `(pk, root, m')`. -/
def itsrReplayer (pk : prims.PkSeed) (root : prims.Y) (m m' : List Byte) :
    KeyedHash.ITSRAdversary (itsrProblem vp prims) where
  main := do
    let R ← (unifSpec + KeyedHash.ITSRTargetSpec (prims.PkSeed × prims.Y × List Byte) prims.Y).query
      (Sum.inr (pk, root, m))
    pure (R, pk, root, m')

/-- ITSR can be won: if `H_msg` has a randomizer-independent collision `m ≠ m'`, `itsrReplayer`
wins with probability `1`. -/
theorem itsrReplayer_adv_one (pk : prims.PkSeed) (root : prims.Y) (m m' : List Byte)
    (hne : m' ≠ m) (hcol : ∀ R, prims.Hmsg R pk root m' = prims.Hmsg R pk root m) :
    KeyedHash.ITSRAdvantage (itsrReplayer (vp := vp) pk root m m') = 1 := by
  rw [KeyedHash.ITSRAdvantage_eq_evalDist_experiment]
  apply prTrue_eq_one_of_support
  intro x hx
  simp [KeyedHash.ITSRExperiment, KeyedHash.ITSRAdversary.run,
    itsrReplayer, KeyedHash.ITSROracles] at hx
  obtain ⟨R, -, rfl⟩ := hx
  rw [decide_eq_true_eq]
  refine ⟨by simp [hne], fun i hi => ?_⟩
  have h : (itsrProblem vp prims).khf.hash R (pk, root, m') =
      (itsrProblem vp prims).khf.hash R (pk, root, m) := hcol R
  simp only [KeyedHash.ITSRProblem.indexSet] at hi
  rw [h] at hi
  simpa [KeyedHash.ITSRProblem.targetIndexSet, KeyedHash.ITSRProblem.indexSet] using hi

/-! ## SM-DT-OpenPRE -/

/-- SM-DT-OpenPRE can be lost: the adversary that commits to no target has advantage `0`. -/
theorem openPre_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage
      (prob := forsOpenPreProblem vp prims pkSeedDist)
      ⟨Unit, pure ((), []), fun _ _ _ => pure (0, default)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.experiment,
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.initializeTargets,
    TweakableHash.SourceFinalValidity.State.initial] at hx
  exact hx.2

/-- The SM-DT-OpenPRE adversary that commits to the single tweak `t`, opens nothing, and
answers `y₀` for target `0`. -/
def openPreInverter (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (y₀ : prims.Y) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist) where
  State := Unit
  pick := pure ((), [t])
  find := fun _ _ _ => pure (0, y₀)

/-- SM-DT-OpenPRE can be won: if `F(·, t, ·)` takes the value `F(pk, t, y₀)` everywhere,
`openPreInverter` wins with probability `1`.
(`0 < openPreTargets vp` always holds: `openPreTargets_pos`.) -/
theorem openPreInverter_adv_one (pkSeedDist : ProbComp prims.PkSeed) (h0 : 0 < openPreTargets vp)
    (t : prims.AdrsKey) (y₀ : prims.Y)
    (hconst : ∀ pk x, prims.Thash pk t [y₀] = prims.Thash pk t [x]) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage
      (openPreInverter (vp := vp) pkSeedDist t y₀) = 1 := by
  apply prTrue_eq_one_of_support
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n, (forsOpenPreProblem vp prims pkSeedDist).numTargets = n + 1 :=
    ⟨openPreTargets vp - 1, by change openPreTargets vp = _; omega⟩
  simp [TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.experiment, openPreInverter, hn,
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.initializeTargets,
    TweakableHash.SourceFinalValidity.State.initial,
    TweakableHash.SourceFinalValidity.State.recordTarget,
    TweakableHash.TweakFresh, TweakableHash.TweakReserved] at hx
  obtain ⟨pk, -, y, -, rfl⟩ := hx
  exact decide_eq_true (hconst pk y)

/-! ## PRF -/

/-- The PRF advantage of a constant distinguisher is `0`. -/
theorem prf_const_adv_zero :
    (skPrf vp prims).prfAdvantage
      (pure true : OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool) = 0 := by
  have h1 : 𝒟[(skPrf vp prims).prfRealExperiment
      (pure true : OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool)]
      {true} = 1 :=
    prTrue_eq_one_of_support _ (by
      intro x hx; simp [PRFScheme.prfRealExperiment] at hx; exact hx.2)
  have h2 : 𝒟[PRFScheme.prfIdealExperiment
      (pure true : OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool)]
      {true} = 1 :=
    prTrue_eq_one_of_support _ (by
      intro x hx; simp [PRFScheme.prfIdealExperiment] at hx; exact hx)
  simp [PRFScheme.prfAdvantage, Measure.boolDist, h1, h2]

/-- The `PRF_msg` advantage of a constant distinguisher is `0`. -/
theorem prfMsg_const_adv_zero :
    (msgPrf vp prims).prfAdvantage
      (pure true : OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool) = 0 := by
  have h1 : 𝒟[(msgPrf vp prims).prfRealExperiment
      (pure true : OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool)]
      {true} = 1 :=
    prTrue_eq_one_of_support _ (by
      intro x hx; simp [PRFScheme.prfRealExperiment] at hx; exact hx.2)
  have h2 : 𝒟[PRFScheme.prfIdealExperiment
      (pure true : OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool)]
      {true} = 1 :=
    prTrue_eq_one_of_support _ (by
      intro x hx; simp [PRFScheme.prfIdealExperiment] at hx; exact hx)
  simp [PRFScheme.prfAdvantage, Measure.boolDist, h1, h2]

/-- The PRF distinguisher that queries one point and tests the answer against `c`. -/
def prfTester (pk : prims.PkSeed) (a : Adrs) (c : prims.Y) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) Bool := do
  let y ← PRFScheme.functionQuery (pk, a)
  pure (decide (y = c))

/-- The PRF game can be won: if `PRF(pk, ·, a)` is the constant `c`, `prfTester` has advantage
`1 − 1/|Y|` (nonzero as soon as `Y` has two elements). -/
theorem prfTester_adv [Fintype prims.Y] (pk : prims.PkSeed) (a : Adrs) (c : prims.Y)
    (hconst : ∀ k, prims.PRF pk k a = c) :
    (skPrf vp prims).prfAdvantage (prfTester pk a c) = 1 - (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
  have h1 : 𝒟[(skPrf vp prims).prfRealExperiment (prfTester pk a c)] {true} = 1 := by
    apply prTrue_eq_one_of_support
    intro x hx
    simp [PRFScheme.prfRealExperiment, prfTester, skPrf, hconst] at hx
    exact hx
  have h2 : 𝒟[PRFScheme.prfIdealExperiment (prfTester pk a c)] {true} =
      (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
    simp [PRFScheme.prfIdealExperiment, prfTester, PRFScheme.functionQuery]
    exact prTrue_map_decide_uniform c
  rw [PRFScheme.prfAdvantage, Measure.boolDist, h1, h2, absDiff_one_inv_card]

/-- The `PRF_msg` distinguisher that queries one point and tests the answer against `c`. -/
def prfMsgTester (r : prims.Y) (m : List Byte) (c : prims.Y) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool := do
  let y ← PRFScheme.functionQuery (r, m)
  pure (decide (y = c))

/-- The `PRF_msg` game can be won: if `PRF_msg(·, r, m)` is the constant `c`, `prfMsgTester` has
advantage `1 − 1/|Y|` (nonzero as soon as `Y` has two elements). -/
theorem prfMsgTester_adv [Fintype prims.Y] (r : prims.Y) (m : List Byte) (c : prims.Y)
    (hconst : ∀ k, prims.PRFmsg k r m = c) :
    (msgPrf vp prims).prfAdvantage (prfMsgTester r m c) =
      1 - (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
  have h1 : 𝒟[(msgPrf vp prims).prfRealExperiment (prfMsgTester r m c)] {true} = 1 := by
    apply prTrue_eq_one_of_support
    intro x hx
    simp [PRFScheme.prfRealExperiment, prfMsgTester, SLHDSA.msgPrfScheme, hconst] at hx
    exact hx
  have h2 : 𝒟[PRFScheme.prfIdealExperiment (prfMsgTester r m c)] {true} =
      (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
    simp [PRFScheme.prfIdealExperiment, prfMsgTester, PRFScheme.functionQuery]
    exact prTrue_map_decide_uniform c
  rw [PRFScheme.prfAdvantage, Measure.boolDist, h1, h2, absDiff_one_inv_card]

/-! ## SM-UD -/

/-- The SM-UD advantage of a constant distinguisher is `0`. -/
theorem ud_const_adv_zero (pkSeedDist : ProbComp prims.PkSeed) (b : Bool) :
    TweakableHash.SM_DT_UD_Advantage (prob := wotsUdProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure b⟩ = 0 := by
  have h : ∀ w, TweakableHash.SM_DT_UD_Experiment w (prob := wotsUdProblem vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure b⟩ = (pkSeedDist >>= fun _ => pure b) := by
    intro w; simp [TweakableHash.SM_DT_UD_Experiment]; rfl
  simp [TweakableHash.SM_DT_UD_Advantage, h, Measure.boolDist_self]

/-- The SM-UD distinguisher that asks for one challenge at tweak `t` and tests it against `c`. -/
def udTester (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (c : prims.Y) :
    TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist) where
  State := Bool
  pick := do
    let r ← (unifSpec + (TweakableHash.SM_DT_UD_challengeSpec prims.AdrsKey prims.Y +
      TweakableHash.collectionSpec (wotsUdProblem vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl t))
    pure (decide (r = some c))
  distinguish := fun b _ => pure b

/-- The SM-UD game can be won: if `F(·, t, ·)` is the constant `c`, `udTester` has advantage
`1 − 1/|Y|` (nonzero as soon as `Y` has two elements). -/
theorem udTester_adv [Fintype prims.Y] (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < wotsChainTargets vp) (t : prims.AdrsKey) (c : prims.Y)
    (hconst : ∀ pk x, prims.Thash pk t [x] = c) :
    TweakableHash.SM_DT_UD_Advantage (udTester (vp := vp) pkSeedDist t c) =
      1 - (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
  have h1 : 𝒟[TweakableHash.SM_DT_UD_Experiment .real (udTester (vp := vp) pkSeedDist t c)]
      {true} = 1 := by
    apply prTrue_eq_one_of_support
    intro x hx
    have hrun : ∀ pk, (TweakableHash.SM_DT_UD_challengeOracle .real
        (wotsUdProblem vp prims pkSeedDist) pk t).run
          (([], []) : TweakableHash.SM_DT_UD_State prims.AdrsKey) = _ :=
      fun pk => TweakableHash.SM_DT_UD_challengeOracle_run_of_fresh_real (by exact h0)
        (by simp [TweakableHash.TweakFresh, TweakableHash.TweakReserved])
    simp [TweakableHash.SM_DT_UD_Experiment, udTester, TweakableHash.SM_DT_UD_oracles, hrun] at hx
    obtain ⟨pk, -, y, -, rfl⟩ := hx
    exact decide_eq_true (hconst pk y)
  have h2 : 𝒟[TweakableHash.SM_DT_UD_Experiment .ideal (udTester (vp := vp) pkSeedDist t c)]
      {true} = (Fintype.card prims.Y : ℝ≥0∞)⁻¹ := by
    have hrun : ∀ pk, (TweakableHash.SM_DT_UD_challengeOracle .ideal
        (wotsUdProblem vp prims pkSeedDist) pk t).run
          (([], []) : TweakableHash.SM_DT_UD_State prims.AdrsKey) = _ :=
      fun pk => TweakableHash.SM_DT_UD_challengeOracle_run_of_fresh_ideal (by exact h0)
        (by simp [TweakableHash.TweakFresh, TweakableHash.TweakReserved])
    simp [TweakableHash.SM_DT_UD_Experiment, udTester, TweakableHash.SM_DT_UD_oracles, hrun]
    exact prTrue_map_decide_uniform c
  rw [TweakableHash.SM_DT_UD_Advantage, Measure.boolDist, h1, h2, absDiff_one_inv_card]

/-! ## The degeneracy conditions are satisfiable: a toy bundle -/

section Toy

/-- A toy primitive bundle for an arbitrary parameter set: one-bit nodes, every hash and PRF
constant.  It satisfies every degeneracy hypothesis of the "won" lemmas above. -/
def toyPrims (p : Params) : Primitives p where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Bool
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ _ _ => false
  PRFmsg := fun _ _ _ => false
  yToBytes := fun b => Vector.replicate p.n (if b then 1 else 0)
  Thash := fun _ _ _ => false
  Hmsg := fun _ _ _ _ => Vector.replicate p.m 0

variable (vp : ValidatedParams)

instance : SampleableType (toyPrims vp.params).Y := inferInstanceAs (SampleableType Bool)
instance : SampleableType (toyPrims vp.params).SkSeed := inferInstanceAs (SampleableType Unit)
instance : SampleableType (toyPrims vp.params).SkPrf := inferInstanceAs (SampleableType Unit)
instance : DecidableEq (toyPrims vp.params).Y := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq (toyPrims vp.params).PkSeed := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq (toyPrims vp.params).AdrsKey := inferInstanceAs (DecidableEq Adrs)
instance : Inhabited (toyPrims vp.params).Y := inferInstanceAs (Inhabited Bool)
instance : Fintype (toyPrims vp.params).Y := inferInstanceAs (Fintype Bool)

theorem toy_tcr (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp (toyPrims vp.params) pkSeedDist),
      TweakableHash.SM_DT_TCR_Advantage B = 1 :=
  tcr_winnable pkSeedDist (tcrTargets_pos vp) fun _ _ _ _ => rfl

theorem toy_pre (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : TweakableHash.SM_DT_PRE_Adversary (wotsPreProblem vp (toyPrims vp.params) pkSeedDist),
      TweakableHash.SM_DT_PRE_Advantage B = 1 :=
  pre_winnable pkSeedDist (wotsChainTargets_pos vp) fun _ _ _ _ => rfl

theorem toy_itsr :
    ∃ B : KeyedHash.ITSRAdversary (itsrProblem vp (toyPrims vp.params)),
      KeyedHash.ITSRAdvantage B = 1 :=
  ⟨_, itsrReplayer_adv_one (prims := toyPrims vp.params) () false [] [0] (by simp) fun _ => rfl⟩

theorem toy_openPre (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
        (forsOpenPreProblem vp (toyPrims vp.params) pkSeedDist),
      TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage B = 1 :=
  ⟨_, openPreInverter_adv_one (prims := toyPrims vp.params) pkSeedDist (openPreTargets_pos vp)
    (default : Adrs) false fun _ _ => rfl⟩

theorem toy_prf :
    ∃ B, (skPrf vp (toyPrims vp.params)).prfAdvantage B = 2⁻¹ := by
  refine ⟨_, (prfTester_adv (prims := toyPrims vp.params) () default false fun _ => rfl).trans ?_⟩
  change 1 - ((Fintype.card Bool : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹
  rw [Fintype.card_bool]
  exact ENNReal.one_sub_inv_two

theorem toy_prfMsg :
    ∃ B, (msgPrf vp (toyPrims vp.params)).prfAdvantage B = 2⁻¹ := by
  refine ⟨_, (prfMsgTester_adv (prims := toyPrims vp.params) false [] false fun _ => rfl).trans ?_⟩
  change 1 - ((Fintype.card Bool : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹
  rw [Fintype.card_bool]
  exact ENNReal.one_sub_inv_two

theorem toy_wotsTcr (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : TweakableHash.SM_DT_TCR_Adversary (wotsTcrProblem vp (toyPrims vp.params) pkSeedDist),
      TweakableHash.SM_DT_TCR_Advantage B = 1 :=
  ⟨_, wotsTcrCollider_adv_one (prims := toyPrims vp.params) pkSeedDist (wotsStepTargets_pos vp)
    (default : Adrs) false true (show (true : Bool) ≠ false by decide) fun _ => rfl⟩

theorem toy_ud (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : TweakableHash.SM_DT_UD_Adversary (wotsUdProblem vp (toyPrims vp.params) pkSeedDist),
      TweakableHash.SM_DT_UD_Advantage B = 2⁻¹ := by
  refine ⟨_, (udTester_adv (prims := toyPrims vp.params) pkSeedDist (wotsChainTargets_pos vp)
    (default : Adrs) false fun _ _ => rfl).trans ?_⟩
  change 1 - ((Fintype.card Bool : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹
  rw [Fintype.card_bool]
  exact ENNReal.one_sub_inv_two

end Toy

#print axioms tcr_trivial_adv_zero
#print axioms tcr_winnable
#print axioms pre_trivial_adv_zero
#print axioms pre_winnable
#print axioms itsr_trivial_adv_zero
#print axioms itsrReplayer_adv_one
#print axioms openPre_trivial_adv_zero
#print axioms openPreInverter_adv_one
#print axioms prf_const_adv_zero
#print axioms prfMsg_const_adv_zero
#print axioms prfTester_adv
#print axioms ud_const_adv_zero
#print axioms udTester_adv
#print axioms wotsTcr_trivial_adv_zero
#print axioms toy_tcr
#print axioms toy_pre
#print axioms toy_itsr
#print axioms toy_openPre
#print axioms toy_prf
#print axioms toy_ud
#print axioms prfMsgTester_adv
#print axioms wotsTcrCollider_adv_one
#print axioms toy_prfMsg
#print axioms toy_wotsTcr

end Reduction
