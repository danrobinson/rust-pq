import Reduction.Lazy.Sparse

/-!
# Step 5 with a sparse table: `bOpenPreS`

`bOpenPreS A` is `bOpenPre A` with the eager `2 ^ 256`-cell table replaced by the sparse table on
the WOTS+ cells only (`sparseOn vp prims (wotsSkIdx vp)`): the FORS secrets are the hidden inputs
of the SM-DT-OpenPRE game and are never sampled by the reduction.
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

/-- The SM-DT-OpenPRE adversary with a sparse table: only the WOTS+ start values are sampled. -/
noncomputable def bOpenPreS (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist) :=
  bOpenPreWith (sparseOn vp prims (wotsSkIdx vp)) A

/-- **Step 5, sparse.** -/
theorem stepOpenPRE_sparse (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepOpenPRE A (bOpenPreS A) := by
  unfold StepOpenPRE
  rw [prTrue_g2Class_eq_sparse hS A .openpre]
  show _ ≤ prTrue (TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.experiment
    (bOpenPreWith (sparseOn vp prims (wotsSkIdx vp)) A))
  rw [op_experiment hS (sparseOn vp prims (wotsSkIdx vp)) A]
  refine le_trans (prTrue_bind_mono _ _ _ fun pkSeed _ =>
    prTrue_bind_mono (sparseTable vp prims) _ _ fun tbl _ =>
      prTrue_bind_pure_mono _ _ (opW pkSeed tbl) fun z _ h =>
        op_win hS pkSeed tbl z (by simpa using (Bool.and_eq_true_iff.1 h).2)) ?_
  refine le_of_eq (prTrue_bind_congr _ _ _ fun pkSeed _ => ?_)
  have hx := evalDist_sparseOn_extract (vp := vp) (prims := prims)
    (is := forsSkIdx vp) (js := wotsSkIdx vp) (structSecIdx_nodup hS)
    (fun T => g2Run A T (idealPk vp prims T pkSeed) >>= fun z => pure (opW pkSeed T z))
  refine (prTrue_congr hx).symm.trans ?_
  refine prTrue_bind_congr _ _ _ fun tbl _ => prTrue_bind_congr _ _ _ fun xs hxs => ?_
  rw [op_tail hS (sparseOn vp prims (wotsSkIdx vp)) A pkSeed tbl xs
    (Tables.length_of_mem_support_sampleList hxs)]

/-! ## Resources -/

/-- `pick` in closed form: `(wotsSkIdx vp).length` uniform samples (and nothing else) are drawn,
they are written at the WOTS+ cells of the all-`default` table, and the committed tweak list is
exactly `forsLeafKeys vp prims`. -/
theorem bOpenPreS_pick (A : Forger vp prims optRand pkSeedDist) :
    (bOpenPreS A).pick =
      (liftM ((fun xs => Tables.updateList (fun _ => default) (wotsSkIdx vp) xs) <$>
          Tables.sampleList prims.Y (wotsSkIdx vp).length) :
        OracleComp (unifSpec + TweakableHash.SourceFinalValidity.collectionSpec
          (forsOpenPreProblem vp prims pkSeedDist).thColl) (SecretTable vp prims)) >>=
        fun tbl => pure (tbl, forsLeafKeys vp prims) := rfl

/-- Every outcome of `pick` commits exactly the list `forsLeafKeys vp prims`. -/
theorem bOpenPreS_pick_snd (A : Forger vp prims optRand pkSeedDist) :
    Prod.snd <$> (bOpenPreS A).pick =
      (liftM (sparseOn vp prims (wotsSkIdx vp)) :
        OracleComp (unifSpec + TweakableHash.SourceFinalValidity.collectionSpec
          (forsOpenPreProblem vp prims pkSeedDist).thColl) (SecretTable vp prims)) >>=
        fun _ => pure (forsLeafKeys vp prims) := by
  show (Prod.snd : SecretTable vp prims × List prims.AdrsKey → List prims.AdrsKey) <$>
    ((liftM (sparseOn vp prims (wotsSkIdx vp)) :
        OracleComp (unifSpec + TweakableHash.SourceFinalValidity.collectionSpec
          (forsOpenPreProblem vp prims pkSeedDist).thColl) (SecretTable vp prims)) >>=
      fun tbl => pure (tbl, forsLeafKeys vp prims)) = _
  rw [map_bind]
  refine bind_congr fun tbl => ?_
  rw [map_pure]

/-- The committed list is duplicate-free of length `openPreTargets vp` (the cap of the game). -/
theorem bOpenPreS_targets (hS : Structural vp prims) :
    (forsLeafKeys vp prims).Nodup ∧ (forsLeafKeys vp prims).length = openPreTargets vp :=
  forsLeafKeys_nodup_length hS

/-- `pick` makes no collection query. -/
theorem bOpenPreS_pick_queryBound (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (bOpenPreS A).pick (fun i => i.isRight = true) 0 := by
  rw [bOpenPreS_pick]
  exact isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftM_isRight _)
    (fun tbl _ => isQueryBoundP_pure _ _ _)

theorem tqb0_pure' {ι : Type} {spec : OracleSpec ι} {α : Type} (x : α) :
    IsTotalQueryBound (pure x : OracleComp spec α) 0 :=
  trivial

/-- `Vector.ofFnM` of `k` computations with `c` queries each makes at most `k * c` queries. -/
theorem tqb_ofFnM' {ι : Type} {spec : OracleSpec ι} {α : Type} {k : ℕ}
    (g : Fin k → OracleComp spec α) (c : ℕ)
    (h : ∀ i, IsTotalQueryBound (g i) c) : IsTotalQueryBound (Vector.ofFnM g) (k * c) := by
  induction k with
  | zero =>
      rw [Vector.ofFnM_zero]
      trivial
  | succ k ih =>
      rw [Vector.ofFnM_succ]
      refine (isTotalQueryBound_bind (ih (fun i => g i.castSucc) (fun i => h i.castSucc))
        fun xs => isTotalQueryBound_bind (n₂ := 0) (h (Fin.last k)) fun a => tqb0_pure' _).mono ?_
      rw [Nat.succ_mul]
      omega

/-- One signature of the reduction makes exactly one opening query per FORS tree. -/
theorem openSign_bound (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims)
    (ys : List prims.Y) (m : List Byte) (R : prims.Y) :
    IsTotalQueryBound (openSign pk tbl ys m R) vp.params.k := by
  unfold openSign
  refine (isTotalQueryBound_bind (n₂ := 0) (tqb_ofFnM' _ 1 fun i =>
    isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) ?_ fun x => tqb0_pure' _) fun fs =>
      tqb0_pure' _).mono (by omega)
  simp [IsTotalQueryBound]

/-- A step of the transcript-recording signing oracle costs what `signR` costs when the
randomizer makes no charged query. -/
theorem logSignOracle_bound_of {ι : Type} {spec : OracleSpec ι}
    (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) (c : ℕ)
    (hr : ∀ log m a, IsQueryBoundP (randomizer log m a) (fun i => i.isRight = true) 0)
    (hs : ∀ m R, IsQueryBoundP (signR m R) (fun i => i.isRight = true) c)
    (msg : List Byte) (log : G2Log prims) :
    IsQueryBoundP ((logSignOracle optRand pk randomizer signR msg).run log)
      (fun i => i.isRight = true) c := by
  simp only [logSignOracle]
  simp
  rw [show c = 0 + (0 + c) by omega]
  exact isQueryBoundP_bind (n := 0) (m := 0 + c)
    (isQueryBoundP_liftM_isRight (hs := spec) (optRand pk))
    (fun a _ => isQueryBoundP_bind (n := 0) (m := c) (hr log msg a)
      (fun R _ => (isQueryBoundP_map_iff _ _ _).2 (hs msg R)))

/-- **Opening queries.**  If the forger makes at most `qs` signing queries, `find` makes at most
`qs * k` opening queries (one per FORS tree per signature). -/
theorem bOpenPreS_find_queryBound (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (st : (bOpenPreS A).State) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP ((bOpenPreS A).find st pkSeed ys) (fun i => i.isRight = true)
      (qs * vp.params.k) := by
  show IsQueryBoundP (runForgerLog A (idealPk vp prims st pkSeed) lazyRandomizerLift
      (openSign (idealPk vp prims st pkSeed) st ys) >>= fun z =>
        pure (openPreAnswer (idealPk vp prims st pkSeed) ys z.2 z.1.1 z.1.2)) _ _
  have key : IsQueryBoundP (runForgerLog A (idealPk vp prims st pkSeed) lazyRandomizerLift
      (openSign (idealPk vp prims st pkSeed) st ys)) (fun i => i.isRight = true)
      (qs * vp.params.k) := by
    unfold runForgerLog
    refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · cases t with
      | inl n => simp at ht
      | inr m =>
        exact logSignOracle_bound_of _ _ _ _
          (fun log m a => isQueryBoundP_liftM_isRight (lazyRandomizer log m a))
          (fun m R => (openSign_bound _ st ys m R).isQueryBoundP) m s
    · cases t with
      | inl n =>
        simp
        exact isQueryBoundP_liftM_isRight (liftM (unifSpec.query n) : ProbComp _)
      | inr m => simp at ht
  have h := isQueryBoundP_bind (m := 0) key
    (fun z _ => isQueryBoundP_pure (fun (i : ℕ ⊕ ℕ) => i.isRight = true)
      (openPreAnswer (idealPk vp prims st pkSeed) ys z.2 z.1.1 z.1.2) 0)
  simpa using h

end Lazy
end Reduction

#print axioms Reduction.Lazy.stepOpenPRE_sparse
#print axioms Reduction.Lazy.bOpenPreS_pick_queryBound
#print axioms Reduction.Lazy.bOpenPreS_find_queryBound
