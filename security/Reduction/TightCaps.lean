import Reduction.HeadlineSplit
import Reduction.Resources
import Reduction.NonVacuity

/-!
# Tight target caps (package W2), generic part and the tight problem instances

Every SM game of the final bound carries a cap `numTargets` on the number of accepted
challenge/target queries.  A larger cap is a *stronger* assumption (more adversaries are
admitted).  Here the caps that are larger than what the reductions use are lowered:

* `thashArityProblemT vp prims pkSeedDist n` — the arity-class SM-TCR game with cap
  `arityTargets vp n` (was `tcrTargets vp` for every class);
* `wotsTcrProblemT vp prims pkSeedDist` — SM-TCR(`F`) on the WOTS+ chains with cap
  `#inst · len · (w − 1)` (`wotsStepTargetsT vp`; was `#inst · len · w`).

**Transfer.**  The cap of an `SM_DT_TCR_Problem` does not occur in the type of the adversary's
programs (only `thColl` does), so an adversary is re-typed by copying its three fields
(`retype`; `retype_choose`, `retype_forge`: literally the same programs).  If in the loose game
the adversary never has more than `M` accepted targets (`M ≤` the loose cap), the two games give
the same answers to every query of every run, hence the *experiments are equal*
(`run_recap_eq`, `experiment_retype_eq`, `advantage_retype_eq`).  No inequality is lost.

Non-vacuity of the two new problem instances: `thashArityT_trivial_adv_zero`,
`thashArityColliderT_adv_one`, `toy_thashArityT`; `wotsTcrT_trivial_adv_zero`,
`wotsTcrColliderT_adv_one`, `toy_wotsTcrT`.

Numeric caps at SHA2-128s (proved by `decide`/`rfl` on closed forms, no `native_decide`):
`thashArityProblemT_cap_128s`, `wotsTcrProblemT_cap_128s`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MeasureTheory

namespace Reduction

open TweakableHash

/-! ## Generic: changing the cap of an SM-TCR problem -/

namespace TightCaps

variable {ι PkSeed Tweak M Y : Type}

/-- The same SM-TCR problem (same hash, same collection) with cap `n`. -/
@[reducible] def recap (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (n : ℕ) :
    SM_DT_TCR_Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := n

/-- The same adversary, typed against the problem with cap `n`: the three fields are copied. -/
def retype {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (n : ℕ)
    (B : SM_DT_TCR_Adversary prob) : SM_DT_TCR_Adversary (recap prob n) where
  State := B.State
  choose := B.choose
  forge := B.forge

theorem retype_State {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (n : ℕ)
    (B : SM_DT_TCR_Adversary prob) : (retype n B).State = B.State := rfl

/-- The re-typed adversary runs the same selection program. -/
theorem retype_choose {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (n : ℕ)
    (B : SM_DT_TCR_Adversary prob) : (retype n B).choose = B.choose := rfl

/-- The re-typed adversary runs the same forging program. -/
theorem retype_forge {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (n : ℕ)
    (B : SM_DT_TCR_Adversary prob) : (retype n B).forge = B.forge := rfl

variable [DecidableEq Tweak]

theorem chal_run_refuse (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak)
    (m : M) (L : List (Tweak × M)) (C : List Tweak)
    (h : prob.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (L, C) = pure (none, (L, C)) := by
  simp [SM_DT_TCR_challengeOracle, h]

theorem chal_run_accept (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak)
    (m : M) (L : List (Tweak × M)) (C : List Tweak)
    (h : ¬ (prob.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t)) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (L, C) =
      pure (some (prob.th.eval pk t m), (L ++ [(t, m)], C)) := by
  simp [SM_DT_TCR_challengeOracle, h]

/-- Every oracle step keeps or extends the list of accepted targets. -/
theorem step_mono (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (q : (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl)).Domain)
    (σ : SM_DT_TCR_State Tweak M) :
    ∀ p ∈ support ((SM_DT_TCR_oracles prob pk q).run σ), σ.1.length ≤ p.2.1.length := by
  obtain ⟨L, C⟩ := σ
  rcases q with n | ⟨t, m⟩ | q
  · intro p hp
    have h : (SM_DT_TCR_oracles prob pk (.inl n)).run (L, C) =
        (fun u => (u, (L, C))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
      simp [SM_DT_TCR_oracles]
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact le_rfl
  · intro p hp
    have horc : SM_DT_TCR_oracles prob pk (.inr (.inl (t, m))) =
        SM_DT_TCR_challengeOracle prob pk (t, m) := rfl
    rw [horc] at hp
    by_cases hc : prob.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
    · rw [chal_run_refuse prob pk t m L C hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact le_rfl
    · rw [chal_run_accept prob pk t m L C hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp
  · intro p hp
    have horc : SM_DT_TCR_oracles prob pk (.inr (.inr q)) =
        collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk q := rfl
    rw [horc] at hp
    by_cases hc : TweakReserved Prod.fst L q.2.1
    · rw [collectionOracle_run_of_challenge_clash Prod.fst q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact le_rfl
    · rw [collectionOracle_run_of_fresh Prod.fst q hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact le_rfl

/-- The list of accepted targets never shrinks during a run. -/
theorem run_mono (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) {α : Type}
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      collectionSpec prob.thColl)) α) (σ : SM_DT_TCR_State Tweak M) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles prob pk) oa).run σ),
      σ.1.length ≤ z.2.1.length := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind q k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff ..).mp hz
    exact (step_mono prob pk q σ p hp).trans (ih p.1 p.2 z hz)

/-- **Lowering the cap does not change a run that stays below the new cap.**  If every final
state of the selection phase in the game with cap `prob.numTargets` has at most `N` accepted
targets, and `N ≤ prob.numTargets`, then the same program has the same output distribution
(result and game state) in the game with cap `N`: no query is answered differently. -/
theorem run_recap_eq (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (N : ℕ)
    (hN : N ≤ prob.numTargets) (pk : PkSeed) {α : Type}
    (oa : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      collectionSpec prob.thColl)) α) (σ : SM_DT_TCR_State Tweak M)
    (h : ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles prob pk) oa).run σ), z.2.1.length ≤ N) :
    (simulateQ (SM_DT_TCR_oracles (recap prob N) pk) oa).run σ =
      (simulateQ (SM_DT_TCR_oracles prob pk) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at h ⊢
    have hcont : ∀ p ∈ support ((SM_DT_TCR_oracles prob pk q).run σ),
        (simulateQ (SM_DT_TCR_oracles (recap prob N) pk) (k p.1)).run p.2 =
          (simulateQ (SM_DT_TCR_oracles prob pk) (k p.1)).run p.2 := fun p hp =>
      ih p.1 p.2 fun z hz => h z ((mem_support_bind_iff ..).mpr ⟨p, hp, hz⟩)
    have hstep : (SM_DT_TCR_oracles (recap prob N) pk q).run σ =
        (SM_DT_TCR_oracles prob pk q).run σ := by
      obtain ⟨L, C⟩ := σ
      rcases q with n | ⟨t, m⟩ | q
      · rfl
      · have horc : SM_DT_TCR_oracles prob pk (.inr (.inl (t, m))) =
            SM_DT_TCR_challengeOracle prob pk (t, m) := rfl
        have horc' : SM_DT_TCR_oracles (recap prob N) pk (.inr (.inl (t, m))) =
            SM_DT_TCR_challengeOracle (recap prob N) pk (t, m) := rfl
        rw [horc, horc']
        by_cases hc : prob.numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t
        · have hc' : (recap prob N).numTargets ≤ L.length ∨ ¬ TweakFresh Prod.fst L C t :=
            hc.imp (fun h1 => hN.trans h1) id
          rw [chal_run_refuse prob pk t m L C hc, chal_run_refuse (recap prob N) pk t m L C hc']
        · by_cases hlt : L.length < N
          · have hc' : ¬ ((recap prob N).numTargets ≤ L.length ∨
                ¬ TweakFresh Prod.fst L C t) := by
              rintro (h1 | h1)
              · exact absurd h1 (Nat.not_le.mpr hlt)
              · exact hc (Or.inr h1)
            rw [chal_run_accept prob pk t m L C hc,
              chal_run_accept (recap prob N) pk t m L C hc']
          · exfalso
            have hrun := chal_run_accept prob pk t m L C hc
            have horc2 : SM_DT_TCR_oracles prob pk (.inr (.inl (t, m))) =
                SM_DT_TCR_challengeOracle prob pk (t, m) := rfl
            obtain ⟨z, hz⟩ := support_nonempty
              ((simulateQ (SM_DT_TCR_oracles prob pk) (k (some (prob.th.eval pk t m)))).run
                (L ++ [(t, m)], C))
            have hle := run_mono prob pk _ _ z hz
            have hz' := h z ((mem_support_bind_iff ..).mpr
              ⟨(some (prob.th.eval pk t m), (L ++ [(t, m)], C)), by
                rw [horc2, hrun]; simp, hz⟩)
            simp only [List.length_append, List.length_singleton] at hle
            omega
      · rfl
    rw [hstep]
    exact bind_congr_of_forall_mem_support _ hcont

variable [DecidableEq M] [DecidableEq Y]

/-- **Equality of the experiments.**  If the adversary `B` never has more than `N` accepted
targets in the game with the loose cap, and `N` is at most the loose cap, then `B` re-typed
against the tight-cap problem plays exactly the same experiment. -/
theorem experiment_retype_eq {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (N : ℕ)
    (hN : N ≤ prob.numTargets) (B : SM_DT_TCR_Adversary prob)
    (h : ∀ pk, ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles prob pk) B.choose).run ([], [])),
      z.2.1.length ≤ N) :
    SM_DT_TCR_Experiment (retype N B) = SM_DT_TCR_Experiment B := by
  unfold SM_DT_TCR_Experiment
  refine bind_congr fun pk => ?_
  have := run_recap_eq prob N hN pk B.choose ([], []) (h pk)
  exact congrArg (· >>= _) this

/-- **Equality of the advantages** under the hypotheses of `experiment_retype_eq`. -/
theorem advantage_retype_eq {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (N : ℕ)
    (hN : N ≤ prob.numTargets) (B : SM_DT_TCR_Adversary prob)
    (h : ∀ pk, ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles prob pk) B.choose).run ([], [])),
      z.2.1.length ≤ N) :
    SM_DT_TCR_Advantage (retype N B) = SM_DT_TCR_Advantage B := by
  unfold SM_DT_TCR_Advantage
  rw [experiment_retype_eq N hN B h]

#print axioms run_recap_eq
#print axioms advantage_retype_eq

end TightCaps

/-- Membership in the support of a mapped computation, without the membership fact about the
sampler (which tactics should not see for table samplers). -/
theorem exists_of_mem_support_map {α β : Type} (mx : ProbComp α) (f : α → β) (z : β)
    (h : z ∈ support (f <$> mx)) : ∃ x, f x = z := by
  simp only [support_map, Set.mem_image] at h
  obtain ⟨x, -, rfl⟩ := h
  exact ⟨x, rfl⟩

/-! ## The tight problem instances -/

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ### Arity classes `F`, `H`, `T_len`, `T_k` -/

-- Unification must not try to decide `arityTargets vp n =?= tcrTargets vp` by evaluation, nor
-- unfold the adversary when comparing it with its re-typed copy.
attribute [local irreducible] arityTargets tcrTargets

variable (vp prims) in
/-- **SM-TCR on `Thash` restricted to inputs of arity `n`, with the tight cap.**  The same game
as `thashArityProblem vp prims pkSeedDist n` (same target function, same collection oracle)
except that at most `arityTargets vp n` targets are accepted — the number of arity-`n` hash calls
of the key structure, which is exactly what `bTcrArS n A` registers — instead of
`tcrTargets vp` (the number of hash calls of all arities). -/
def thashArityProblemT (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) :
    SM_DT_TCR_Problem Unit prims.PkSeed prims.AdrsKey {xs : List prims.Y // xs.length = n}
      prims.Y :=
  TightCaps.recap (thashArityProblem vp prims pkSeedDist n) (arityTargets vp n)

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- Unfolded: the class problem of `Reduction/TcrSplit.lean` with cap `arityTargets vp n`. -/
theorem thashArityProblemT_eq_classProblem (n : ℕ) :
    thashArityProblemT vp prims pkSeedDist n =
      TcrSplit.classProblem (thashList vp prims pkSeedDist) (fun xs => xs.length = n)
        (arityTargets vp n) := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem thashArityProblemT_numTargets (n : ℕ) :
    (thashArityProblemT vp prims pkSeedDist n).numTargets = arityTargets vp n := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem thashArityProblemT_thColl (n : ℕ) :
    (thashArityProblemT vp prims pkSeedDist n).thColl = thashColl vp prims := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem thashArityProblem_numTargets (n : ℕ) :
    (thashArityProblem vp prims pkSeedDist n).numTargets = tcrTargets vp := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem wotsTcrProblem_numTargets :
    (wotsTcrProblem vp prims pkSeedDist).numTargets = wotsStepTargets vp := rfl

/-- The per-class count is at most the total count (no hypothesis). -/
theorem arityTargets_le_tcrTargets (vp : ValidatedParams) (n : ℕ) :
    arityTargets vp n ≤ tcrTargets vp := by
  rw [← mf_all_countP (vp := vp) n, tcrTargets, ← mf_all_length]
  exact List.countP_le_length

/-- **The arity-`n` adversary against the tight-cap game**: `bTcrArS n A` re-typed (same state
type, same `choose`, same `forge`: `bTcrArST_choose`, `bTcrArST_forge`). -/
noncomputable def bTcrArST (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n) :=
  TightCaps.retype (prob := thashArityProblem vp prims pkSeedDist n) (arityTargets vp n)
    (bTcrArS n A)

attribute [local irreducible] bTcrArS in
theorem bTcrArST_choose (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArST n A).choose = (bTcrArS n A).choose := rfl

attribute [local irreducible] bTcrArS in
theorem bTcrArST_forge (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArST n A).forge = (bTcrArS n A).forge := rfl

set_option linter.constructorNameAsVariable false in
/-- `bTcrArS n A` stays within the tight cap in its loose-cap game. -/
theorem bTcrArS_within (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArS n A).choose).run ([], [])), z.2.1.length ≤ arityTargets vp n := by
  intro z hz
  rw [bTcrArS_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact (bTcrArS_targets hS n tbl pk).1.le

/-- **Transfer, arity classes: the experiments are equal.** -/
theorem bTcrArST_experiment_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Experiment (bTcrArST n A) = SM_DT_TCR_Experiment (bTcrArS n A) :=
  TightCaps.experiment_retype_eq (arityTargets vp n) (arityTargets_le_tcrTargets vp n)
    (bTcrArS n A) (bTcrArS_within hS n A)

/-- **Transfer, arity classes: equal advantages.** -/
theorem bTcrArST_advantage_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrArST n A) = SM_DT_TCR_Advantage (bTcrArS n A) :=
  TightCaps.advantage_retype_eq (arityTargets vp n) (arityTargets_le_tcrTargets vp n)
    (bTcrArS n A) (bTcrArS_within hS n A)

attribute [local irreducible] bTcrArS in
/-- **The `choose` phase of `bTcrArST n A` in the tight-cap game is the `choose` phase of
`bTcrArS n A` in the loose-cap game** (same distribution on results and game states; the latter
is given explicitly by `bTcrArS_choose_run`: one sparse table, `gState` of the honest calls). -/
theorem bTcrArST_run_eq (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArST n A).choose).run ([], []) =
      (simulateQ (SM_DT_TCR_oracles (thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArS n A).choose).run ([], []) :=
  TightCaps.run_recap_eq (thashArityProblem vp prims pkSeedDist n) (arityTargets vp n)
    (arityTargets_le_tcrTargets vp n) pk (bTcrArS n A).choose ([], [])
    (bTcrArS_within hS n A pk)

set_option linter.constructorNameAsVariable false in
/-- The cap of the tight class game is attained by `bTcrArST n A` in every run. -/
theorem bTcrArST_targets_eq_cap (hS : Structural vp prims) (n : ℕ)
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (thashArityProblemT vp prims pkSeedDist n) pk)
        (bTcrArST n A).choose).run ([], [])),
      z.2.1.length = (thashArityProblemT vp prims pkSeedDist n).numTargets := by
  intro z hz
  rw [bTcrArST_run_eq hS n A pk, bTcrArS_choose_run hS n A pk] at hz
  obtain ⟨tbl, rfl⟩ := exists_of_mem_support_map _ _ z hz
  exact (bTcrArS_targets hS n tbl pk).1

/-! ### WOTS+ chains -/

/-- Tight cap of SM-TCR(`F`) on the WOTS+ chains: `#inst · len · (w − 1)` (a chain has `w − 1`
steps). -/
def wotsStepTargetsT (vp : ValidatedParams) : ℕ :=
  (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))

theorem wotsStepTargetsT_le (vp : ValidatedParams) : wotsStepTargetsT vp ≤ wotsStepTargets vp := by
  rw [Resources.wotsStepTargets_eq, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

variable (vp prims) in
/-- **SM-TCR on `F` for the WOTS+ chain steps, with the tight cap** `#inst · len · (w − 1)`
(`wotsTcrProblem` has `#inst · len · w`); same hash `fHash`, same collection `thashColl`. -/
def wotsTcrProblemT (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_TCR_Problem Unit prims.PkSeed prims.AdrsKey prims.Y prims.Y :=
  TightCaps.recap (wotsTcrProblem vp prims pkSeedDist) (wotsStepTargetsT vp)

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- Unfolded: `F` as target function, the whole `Thash` as collection, cap
`wotsStepTargetsT vp`. -/
theorem wotsTcrProblemT_eq :
    wotsTcrProblemT vp prims pkSeedDist =
      { th := fHash vp prims pkSeedDist, thColl := thashColl vp prims,
        numTargets := wotsStepTargetsT vp } := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem wotsTcrProblemT_numTargets :
    (wotsTcrProblemT vp prims pkSeedDist).numTargets =
      (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)) := rfl

/-- **The chain SM-TCR adversary against the tight-cap game**: `rTcr pkSeedDist W` re-typed
(same state type, same `choose`, same `forge`). -/
noncomputable def rTcrT (pkSeedDist : ProbComp prims.PkSeed) (W : WotsGame.Adversary prims) :
    SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist) :=
  TightCaps.retype (prob := wotsTcrProblem vp prims pkSeedDist) (wotsStepTargetsT vp)
    (rTcr pkSeedDist W)

theorem rTcrT_choose (W : WotsGame.Adversary prims) :
    (rTcrT (vp := vp) pkSeedDist W).choose = (rTcr pkSeedDist W).choose := rfl

theorem rTcrT_forge (W : WotsGame.Adversary prims) :
    (rTcrT (vp := vp) pkSeedDist W).forge = (rTcr pkSeedDist W).forge := rfl

/-- **Transfer, WOTS+ chains: the experiments are equal** (for every WOTS adversary `W`). -/
theorem rTcrT_experiment_eq (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    SM_DT_TCR_Experiment (rTcrT (vp := vp) pkSeedDist W) =
      SM_DT_TCR_Experiment (rTcr pkSeedDist W) :=
  TightCaps.experiment_retype_eq (wotsStepTargetsT vp) (wotsStepTargetsT_le vp)
    (rTcr pkSeedDist W) fun pk z hz => (Resources.rTcr_targets_le pkSeedDist hS W pk z hz).2.2

/-- **Transfer, WOTS+ chains: equal advantages.** -/
theorem rTcrT_advantage_eq (hS : Structural vp prims) (W : WotsGame.Adversary prims) :
    SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist W) =
      SM_DT_TCR_Advantage (rTcr pkSeedDist W) :=
  TightCaps.advantage_retype_eq (wotsStepTargetsT vp) (wotsStepTargetsT_le vp)
    (rTcr pkSeedDist W) fun pk z hz => (Resources.rTcr_targets_le pkSeedDist hS W pk z hz).2.2

/-- In the tight-cap game `rTcrT W` accepts at most the cap (restated for the new game). -/
theorem rTcrT_targets_le (hS : Structural vp prims) (W : WotsGame.Adversary prims)
    (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblemT vp prims pkSeedDist) pk)
        (rTcrT (vp := vp) pkSeedDist W).choose).run ([], [])),
      z.2.1.length ≤ (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)) := by
  intro z hz
  have h := TightCaps.run_recap_eq (wotsTcrProblem vp prims pkSeedDist) (wotsStepTargetsT vp)
    (wotsStepTargetsT_le vp) pk (rTcr pkSeedDist W).choose ([], [])
    (fun z hz => (Resources.rTcr_targets_le pkSeedDist hS W pk z hz).2.2)
  have hz' : z ∈ support ((simulateQ (SM_DT_TCR_oracles (wotsTcrProblem vp prims pkSeedDist) pk)
      (rTcr pkSeedDist W).choose).run ([], [])) := h ▸ hz
  exact (Resources.rTcr_targets_le pkSeedDist hS W pk z hz').2.2

/-! ## Non-vacuity of the new problem instances -/

/-- The tight arity-`n` game can be lost: no target, advantage `0`. -/
theorem thashArityT_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) :
    SM_DT_TCR_Advantage (prob := thashArityProblemT vp prims pkSeedDist n)
      ⟨Unit, pure (), fun _ _ => pure (0, arityDefault prims n)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [SM_DT_TCR_Experiment] at hx
  exact hx.2

/-- The adversary against the tight arity-`n` game that commits to `(t, x)` and answers `y`. -/
def thashArityColliderT (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) (t : prims.AdrsKey)
    (x y : {xs : List prims.Y // xs.length = n}) :
    SM_DT_TCR_Adversary (thashArityProblemT vp prims pkSeedDist n) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (SM_DT_TCR_challengeSpec prims.AdrsKey
        {xs : List prims.Y // xs.length = n} prims.Y +
      collectionSpec (thashArityProblemT vp prims pkSeedDist n).thColl)).query
        (Sum.inr (Sum.inl (t, x)))
    pure ()
  forge := fun _ _ => pure (0, y)

/-- The tight arity-`n` game can be won whenever its cap is positive: a seed-independent
collision between two inputs of arity `n` at some tweak gives advantage `1`. -/
theorem thashArityColliderT_adv_one (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ)
    (h0 : 0 < arityTargets vp n) (t : prims.AdrsKey) (x y : {xs : List prims.Y // xs.length = n})
    (hne : y ≠ x) (hcol : ∀ pk, prims.Thash pk t y.1 = prims.Thash pk t x.1) :
    SM_DT_TCR_Advantage (thashArityColliderT (vp := vp) pkSeedDist n t x y) = 1 := by
  apply prTrue_eq_one_of_support
  intro b hb
  have hrun : ∀ pk, (SM_DT_TCR_challengeOracle (thashArityProblemT vp prims pkSeedDist n) pk
      (t, x)).run (([], []) : SM_DT_TCR_State prims.AdrsKey
        {xs : List prims.Y // xs.length = n}) = _ :=
    fun pk => SM_DT_TCR_challengeOracle_run_of_fresh (by exact h0)
      (by simp [TweakFresh, TweakReserved])
  simp [SM_DT_TCR_Experiment, thashArityColliderT, SM_DT_TCR_oracles, hrun] at hb
  obtain ⟨pk, -, rfl⟩ := hb
  have h : (thashArityProblemT vp prims pkSeedDist n).th.eval pk t y =
      (thashArityProblemT vp prims pkSeedDist n).th.eval pk t x := hcol pk
  simp [hne, h]

/-- The tight cap of the `F` class is positive for every parameter set. -/
theorem arityTargets_one_pos (vp : ValidatedParams) : 0 < arityTargets vp 1 := by
  have hk := vp.valid.k_pos
  have h2 : 0 < 2 ^ vp.params.h * (vp.params.k * 2 ^ vp.params.a) := by positivity
  have hle : 2 ^ vp.params.h * (vp.params.k * 2 ^ vp.params.a) ≤ arityTargets vp 1 := by
    unfold arityTargets
    have e : arInd 1 1 = 1 := rfl
    rw [e, Nat.mul_one]
    refine le_trans (Nat.mul_le_mul_left _ ?_) (Nat.le_add_right _ _)
    refine le_trans (Nat.mul_le_mul_left _ ?_) (Nat.le_add_right _ _)
    exact Nat.le_add_right _ _
  omega

/-- On the constant toy bundle the tight arity-`1` game is won with probability `1`. -/
theorem toy_thashArityT (vp : ValidatedParams)
    (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : SM_DT_TCR_Adversary (thashArityProblemT vp (toyPrims vp.params) pkSeedDist 1),
      SM_DT_TCR_Advantage B = 1 :=
  ⟨_, thashArityColliderT_adv_one (prims := toyPrims vp.params) pkSeedDist 1
    (arityTargets_one_pos vp)
    (default : Adrs) ⟨[false], rfl⟩ ⟨[true], rfl⟩
    (fun h => absurd (List.cons.inj (congrArg Subtype.val h)).1
      (show (true : Bool) ≠ false by decide)) fun _ => rfl⟩

/-- The tight WOTS+ SM-TCR game can be lost. -/
theorem wotsTcrT_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) :
    SM_DT_TCR_Advantage (prob := wotsTcrProblemT vp prims pkSeedDist)
      ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [SM_DT_TCR_Experiment] at hx
  exact hx.2

/-- The adversary against the tight WOTS+ SM-TCR game that commits to `(t, x)` and answers
`y`. -/
def wotsTcrColliderT (pkSeedDist : ProbComp prims.PkSeed) (t : prims.AdrsKey) (x y : prims.Y) :
    SM_DT_TCR_Adversary (wotsTcrProblemT vp prims pkSeedDist) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
      collectionSpec (wotsTcrProblemT vp prims pkSeedDist).thColl)).query
        (Sum.inr (Sum.inl (t, x)))
    pure ()
  forge := fun _ _ => pure (0, y)

/-- The tight WOTS+ SM-TCR game can be won whenever its cap is positive. -/
theorem wotsTcrColliderT_adv_one (pkSeedDist : ProbComp prims.PkSeed)
    (h0 : 0 < wotsStepTargetsT vp) (t : prims.AdrsKey) (x y : prims.Y) (hne : y ≠ x)
    (hcol : ∀ pk, prims.Thash pk t [y] = prims.Thash pk t [x]) :
    SM_DT_TCR_Advantage (wotsTcrColliderT (vp := vp) pkSeedDist t x y) = 1 := by
  apply prTrue_eq_one_of_support
  intro b hb
  have hrun : ∀ pk, (SM_DT_TCR_challengeOracle (wotsTcrProblemT vp prims pkSeedDist) pk
      (t, x)).run (([], []) : SM_DT_TCR_State prims.AdrsKey prims.Y) = _ :=
    fun pk => SM_DT_TCR_challengeOracle_run_of_fresh (by exact h0)
      (by simp [TweakFresh, TweakReserved])
  simp [SM_DT_TCR_Experiment, wotsTcrColliderT, SM_DT_TCR_oracles, hrun] at hb
  obtain ⟨pk, -, rfl⟩ := hb
  have h : (wotsTcrProblemT vp prims pkSeedDist).th.eval pk t y =
      (wotsTcrProblemT vp prims pkSeedDist).th.eval pk t x := hcol pk
  simp [hne, h]

/-- The tight chain cap is positive for every parameter set (`w = 2^lgw ≥ 2`). -/
theorem wotsStepTargetsT_pos (vp : ValidatedParams) : 0 < wotsStepTargetsT vp := by
  have h1 : 0 < (wotsInsts vp).length := by
    rw [Resources.wotsInsts_length]; exact wotsInstanceCount_pos vp
  have h2 := vp.params.len_pos
  have h3 : 0 < vp.params.w - 1 := by
    have := vp.valid.lgw_pos
    have hw : 2 ^ 1 ≤ 2 ^ vp.params.lgw := Nat.pow_le_pow_right (by norm_num) this
    have : vp.params.w = 2 ^ vp.params.lgw := rfl
    omega
  exact Nat.mul_pos h1 (Nat.mul_pos h2 h3)

/-- On the constant toy bundle the tight WOTS+ SM-TCR game is won with probability `1`. -/
theorem toy_wotsTcrT (vp : ValidatedParams)
    (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : SM_DT_TCR_Adversary (wotsTcrProblemT vp (toyPrims vp.params) pkSeedDist),
      SM_DT_TCR_Advantage B = 1 :=
  ⟨_, wotsTcrColliderT_adv_one (prims := toyPrims vp.params) pkSeedDist (wotsStepTargetsT_pos vp)
    (default : Adrs) false true (show (true : Bool) ≠ false by decide) fun _ => rfl⟩

/-! ## The tight caps at SLH-DSA-SHA2-128s -/

/-- **Caps of the four tight class games at SHA2-128s**:
`F`: `533756792467910173399552 ≈ 2^78.82`; `H`: `528785142244921151848447 ≈ 2^78.81`;
`T_len`: `9241421688590303744 ≈ 2^63.003`; `T_k`: `9223372036854775808 = 2^63`
(old cap of each: `tcrTargets = 1062560399506556770327551 ≈ 2^79.81`). -/
theorem thashArityProblemT_cap_128s (pkSeedDist : ProbComp Link.prims.PkSeed) :
    (thashArityProblemT Link.vp Link.prims pkSeedDist 1).numTargets =
        533756792467910173399552 ∧
    (thashArityProblemT Link.vp Link.prims pkSeedDist 2).numTargets =
        528785142244921151848447 ∧
    (thashArityProblemT Link.vp Link.prims pkSeedDist Link.vp.params.len).numTargets =
        9241421688590303744 ∧
    (thashArityProblemT Link.vp Link.prims pkSeedDist Link.vp.params.k).numTargets =
        9223372036854775808 ∧
    (thashArityProblem Link.vp Link.prims pkSeedDist 1).numTargets =
        1062560399506556770327551 :=
  ⟨(thashArityProblemT_numTargets 1).trans arityTargets_128s.1,
    (thashArityProblemT_numTargets 2).trans arityTargets_128s.2.1,
    (thashArityProblemT_numTargets Link.vp.params.len).trans arityTargets_128s.2.2.1,
    (thashArityProblemT_numTargets Link.vp.params.k).trans arityTargets_128s.2.2.2.1,
    (thashArityProblem_numTargets 1).trans Resources.tcrTargets_128s_val⟩

/-- **Cap of the tight chain game at SHA2-128s**: `4851746386509909465600 ≈ 2^72.04`
(old cap `5175196145610570096640 ≈ 2^72.13`). -/
theorem wotsTcrProblemT_cap_128s (pkSeedDist : ProbComp Link.prims.PkSeed) :
    (wotsTcrProblemT Link.vp Link.prims pkSeedDist).numTargets = 4851746386509909465600 ∧
    (wotsTcrProblem Link.vp Link.prims pkSeedDist).numTargets = 5175196145610570096640 :=
  ⟨wotsTcrProblemT_numTargets.trans Resources.wotsExecutedSteps_128s,
    wotsTcrProblem_numTargets.trans Resources.wotsStepTargets_128s_val⟩

#print axioms bTcrArST_experiment_eq
#print axioms bTcrArST_advantage_eq
#print axioms bTcrArST_run_eq
#print axioms bTcrArST_targets_eq_cap
#print axioms rTcrT_experiment_eq
#print axioms rTcrT_advantage_eq
#print axioms rTcrT_targets_le
#print axioms thashArityT_trivial_adv_zero
#print axioms thashArityColliderT_adv_one
#print axioms toy_thashArityT
#print axioms wotsTcrT_trivial_adv_zero
#print axioms wotsTcrColliderT_adv_one
#print axioms toy_wotsTcrT
#print axioms thashArityProblemT_cap_128s
#print axioms wotsTcrProblemT_cap_128s

end Reduction
