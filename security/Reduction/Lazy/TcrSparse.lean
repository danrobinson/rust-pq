import Reduction.Lazy.Sparse
import Reduction.TCR

/-!
# Step 6 with a sparse table: `bTcrS`

`bTcrWith my A` is `bTcr A` with the table sampler as a parameter; `bTcrS A` instantiates it with
the sparse table of the key structure (`sparseTable vp prims`, `(structSecIdx vp).length` uniform
samples).  The proofs of the `choose` run and of the experiment are those of `Reduction.TCR`,
which are pointwise in the table.

Resources of `bTcrS A`:
* `choose` draws exactly `(structSecIdx vp).length` uniform values (`sparseTable_eq`) and submits
  the challenges `honestCalls tbl pk`: `tcrTargets vp` of them, with distinct tweaks, none refused
  (`bTcrS_choose_run`, `bTcrS_targets`);
* `forge` has type `State → PkSeed → ProbComp _`: it has no oracle access at all.  Its local
  work is not small: the state is the table only, so `forge` recomputes `honestCalls tbl pk`,
  i.e. the whole key structure at the revealed seed — exactly `tcrTargets vp` hash evaluations
  (`≈ 2^79.81` at SHA2-128s; `Resources2.tcr_structure_exact`, `Reduction/Resources2Tcr.lean`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Lazy

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The SM-TCR adversary built from a forger, with the table sampler `my` as a parameter
(`bTcr A = bTcrWith (sampleTable vp prims) A` by `rfl`). -/
noncomputable def bTcrWith (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist) where
  State := SecretTable vp prims
  choose := do
    let tbl ← (monadLift my :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey (List prims.Y)
        prims.Y + TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
        (SecretTable vp prims))
    structureVia (vp := vp) (prims := prims)
      (fun key xs => do
        let r ← ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey (List prims.Y)
            prims.Y + TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
            (Sum.inr (Sum.inl (key, xs))) :
          OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
            (List prims.Y) prims.Y +
            TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
            (Option prims.Y))
        pure (r.getD default))
      (fun a => pure (secretOf vp prims tbl a))
    return tbl
  forge := fun tbl pkSeed => do
    let pk := idealPk vp prims tbl pkSeed
    let ((msg, sig), _) ← g2Run A tbl pk
    return (findCollision pkSeed (honestCalls tbl pkSeed) (verifyCalls pk msg sig)).getD (0, [])

theorem bTcr_eq_bTcrWith (A : Forger vp prims optRand pkSeedDist) :
    bTcr A = bTcrWith (sampleTable vp prims) A := rfl

/-- The `choose` phase of `bTcrWith`, run in the SM-TCR game at seed `pk`, records exactly
`honestCalls tbl pk` as its challenge history (and returns `tbl`). -/
theorem bTcrWith_choose_run (hS : Structural vp prims)
    (my : ProbComp (SecretTable vp prims)) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
        (bTcrWith my A).choose).run ([], []) =
      (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> my := by
  have hstruct : ∀ tbl : SecretTable vp prims,
      simulateQ (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
        (structureVia (vp := vp) (prims := prims)
          (fun key xs => do
            let r ← ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
                (Sum.inr (Sum.inl (key, xs))) :
              OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
                (Option prims.Y))
            pure (r.getD default))
          (fun a => pure (secretOf vp prims tbl a))) =
      simulateQ (chalImpl (vp := vp) pkSeedDist pk) (structureFree tbl) := by
    intro tbl
    have h1 := structureVia_natural (vp := vp)
      (simulateQ' (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk))
      (fun key xs => do
            let r ← ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
                (Sum.inr (Sum.inl (key, xs))) :
              OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
                (Option prims.Y))
            pure (r.getD default))
      (fun a => pure (secretOf vp prims tbl a))
    have h2 := structureVia_natural (vp := vp)
      (simulateQ' (chalImpl (vp := vp) (prims := prims) pkSeedDist pk))
      (fun key xs => (liftM ((thSpec prims).query (key, xs)) : OracleComp (thSpec prims) prims.Y))
      (fun a => pure (secretOf vp prims tbl a))
    simp only [simulateQ_spec_query, simulateQ_pure, simulateQ_bind] at h1 h2
    unfold structureFree
    rw [h1, h2]
    unfold chalImpl TweakableHash.SM_DT_TCR_oracles
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    rfl
  have hnl := honestCalls_nodup_length hS
  unfold bTcrWith
  dsimp only
  rw [simulateQ_bind, StateT.run_bind]
  rw [tcrOracles_run_lift, map_eq_bind_pure_comp, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun tbl => ?_
  rw [Function.comp_apply, pure_bind, simulateQ_bind, StateT.run_bind, hstruct tbl,
    chalImpl_run_eq pk _ [] (by rw [← honestCalls_eq_free]; exact (hnl tbl pk).1)
      (by rw [← honestCalls_eq_free]; exact (hnl tbl pk).2.le), pure_bind,
    ← honestCalls_eq_free]
  rfl
/-- The SM-TCR experiment at `bTcrWith my A`, with the `choose` phase evaluated. -/
theorem tcrExperiment_bTcrWith (hS : Structural vp prims)
    (my : ProbComp (SecretTable vp prims)) (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_TCR_Experiment (bTcrWith my A) = (do
      let pkSeed ← pkSeedDist
      let tbl ← my
      let r ← g2Run A tbl (idealPk vp prims tbl pkSeed)
      let jm := (findCollision pkSeed (honestCalls tbl pkSeed)
        (verifyCalls (idealPk vp prims tbl pkSeed) r.1.1 r.1.2)).getD (0, [])
      match (honestCalls tbl pkSeed)[jm.1]? with
      | none => return false
      | some (t, mj) => return decide (jm.2 ≠ mj ∧
          prims.Thash pkSeed t jm.2 = prims.Thash pkSeed t mj)) := by
  unfold TweakableHash.SM_DT_TCR_Experiment
  refine bind_congr fun pkSeed => ?_
  rw [bTcrWith_choose_run hS my A pkSeed]
  rw [map_eq_bind_pure_comp]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr fun tbl => ?_
  refine (pure_bind _ _).trans ?_
  refine (bind_assoc (g2Run A tbl (idealPk vp prims tbl pkSeed)) _ _).trans ?_
  refine bind_congr fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  refine (pure_bind _ _).trans ?_
  dsimp only
  generalize (findCollision pkSeed (honestCalls tbl pkSeed)
    (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).getD (0, []) = jm
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases (honestCalls tbl pkSeed)[j]? with
  | none => rfl
  | some t => rfl
/-- The SM-TCR adversary with the sparse table of the key structure. -/
noncomputable def bTcrS (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist) :=
  bTcrWith (sparseTable vp prims) A

/-- **Step 6, sparse.** -/
theorem stepTCR_sparse (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepTCR A (bTcrS A) := by
  unfold StepTCR
  rw [prTrue_g2Class_eq_sparse hS A .tcr]
  unfold TweakableHash.SM_DT_TCR_Advantage prTrue bTcrS
  rw [tcrExperiment_bTcrWith hS (sparseTable vp prims) A]
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSeed => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun tbl => ?_
  unfold g2ClassAt
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  dsimp only
  by_cases hv : (g2Valid (idealPk vp prims tbl pkSeed) log msg sig &&
      decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr)) = true
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hv
    have hsome := findCollision_isSome_of_tcr hS tbl pkSeed log msg sig hv.1 hv.2
    obtain ⟨⟨j, m⟩, hjm⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨t, ht, hne, heq⟩ := findCollision_sound _ _ _ j m hjm
    rw [hjm]
    simp only [Option.getD_some, ht]
    simp [hne, heq, hv.1, hv.2]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

/-! ## Resources -/

/-- The `choose` phase of `bTcrS`: every challenge of `honestCalls tbl pk` is accepted, and the
recorded challenge history is exactly that list. -/
theorem bTcrS_choose_run (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
        (bTcrS A).choose).run ([], []) =
      (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> sparseTable vp prims :=
  bTcrWith_choose_run hS (sparseTable vp prims) A pk

/-- The challenges have distinct tweaks and there are `tcrTargets vp` of them. -/
theorem bTcrS_targets (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    ((honestCalls tbl pk).map (·.1)).Nodup ∧ (honestCalls tbl pk).length = tcrTargets vp :=
  honestCalls_nodup_length hS tbl pk

/-- The sampler of `bTcrS`: `(structSecIdx vp).length` uniform values, nothing else. -/
theorem sparseTable_eq :
    sparseTable vp prims =
      (fun xs => Tables.updateList (fun _ => default) (structSecIdx vp) xs) <$>
        Tables.sampleList prims.Y (structSecIdx vp).length := rfl

end Lazy
end Reduction

#print axioms Reduction.Lazy.bTcrWith_choose_run
#print axioms Reduction.Lazy.stepTCR_sparse
