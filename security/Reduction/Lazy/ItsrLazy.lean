import Reduction.Lazy.Open
import Reduction.ITSR

/-!
# The lazy ITSR adversary `bItsrL`
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

/-- The game oracle of the ITSR game: the target oracle. -/
abbrev itsrG (prims : Primitives vp.params) : OracleSpec (ItsrIn prims) :=
  KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y

/-- The randomizer of the open ITSR adversary (as `itsrRandomizer`). -/
def itsrRandomizerO (pkSeed : prims.PkSeed) (root : prims.Y) (log : G2Log prims) (m : List Byte)
    (addrnd : prims.Y) : OracleComp (OSpec prims (itsrG prims)) prims.Y :=
  match log.find? (fun e => decide (e.1 = m ∧ e.2.1 = addrnd)) with
  | some e => pure e.2.2
  | none => gameQ prims (itsrG prims) (pkSeed, root, m)

/-- The open program of the ITSR adversary. -/
def itsrOpen (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (OSpec prims (itsrG prims)) (prims.Y × ItsrIn prims) := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OSpec prims (itsrG prims)) prims.PkSeed)
  let root ← openKeygen prims (itsrG prims) pkSeed
  let z ← runForgerLog A ⟨pkSeed, root⟩ (itsrRandomizerO pkSeed root)
    (fun m R => openSign prims (itsrG prims) m pkSeed root R)
  return (z.1.2.randomness, (pkSeed, root, z.1.1))

/-- **The lazy ITSR adversary**: `itsrOpen A` with the secret oracle answered from an
association-list cache, a fresh uniform value being drawn on each miss. -/
noncomputable def bItsrL (A : Forger vp prims optRand pkSeedDist) :
    KeyedHash.ITSRAdversary (itsrProblem vp prims) where
  main := lazyRun (PublicHash.impl prims) (itsrOpen A)

/-- What `bItsr A` does after sampling the seed and the table. -/
noncomputable def itsrBody (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) : OracleComp (itsrSpec prims) (prims.Y × ItsrIn prims) := do
  let z ← runForgerLog A (idealPk vp prims tbl pkSeed)
    (itsrRandomizer pkSeed (idealPk vp prims tbl pkSeed).pkRoot)
    (fun m R => pure (idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R))
  return (z.1.2.randomness, (pkSeed, (idealPk vp prims tbl pkSeed).pkRoot, z.1.1))

theorem bItsr_main_eq (A : Forger vp prims optRand pkSeedDist) :
    (bItsr A).main = (liftM pkSeedDist : OracleComp (itsrSpec prims) prims.PkSeed) >>=
      fun pkSeed => (liftM (sampleTable vp prims) : OracleComp (itsrSpec prims) _) >>=
        fun tbl => itsrBody A tbl pkSeed := rfl

theorem runForgerLog_tbl (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims)
    (pk : PublicKeyCore prims.core)
    (randO : G2Log prims → List Byte → prims.Y → OracleComp (OSpec prims (itsrG prims)) prims.Y)
    (signO : List Byte → prims.Y → OracleComp (OSpec prims (itsrG prims))
      (GeneralScheme.SignatureCore vp prims.core))
    (randC : G2Log prims → List Byte → prims.Y → OracleComp (itsrSpec prims) prims.Y)
    (signC : List Byte → prims.Y → OracleComp (itsrSpec prims)
      (GeneralScheme.SignatureCore vp prims.core))
    (hrand : ∀ log m a, simulateQ (tblImpl (PublicHash.impl prims) g) (randO log m a) =
      randC log m a)
    (hsign : ∀ m R, simulateQ (tblImpl (PublicHash.impl prims) g) (signO m R) = signC m R) :
    simulateQ (tblImpl (PublicHash.impl prims) g) (runForgerLog A pk randO signO) =
      runForgerLog A pk randC signC := by
  unfold runForgerLog
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase]
    exact simulateQ_tblImpl_liftM (PublicHash.impl prims) g (liftM (unifSpec.query n))
  | inr m =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase, logSignOracle, hrand, hsign, simulateQ_tblImpl_liftM]

theorem itsrOpen_tbl (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims) :
    simulateQ (tblImpl (PublicHash.impl prims) g) (itsrOpen A) =
      (liftM pkSeedDist : OracleComp (itsrSpec prims) prims.PkSeed) >>=
        fun pkSeed => itsrBody A g pkSeed := by
  unfold itsrOpen
  simp only [simulateQ_bind, simulateQ_pure]
  rw [simulateQ_tblImpl_liftM]
  refine bind_congr fun pkSeed => ?_
  rw [openKeygen_tbl, pure_bind]
  rw [runForgerLog_tbl A g ⟨pkSeed, idealRoot vp prims g pkSeed⟩ _ _
    (itsrRandomizer pkSeed (idealRoot vp prims g pkSeed))
    (fun m R => pure (idealSign vp prims g m ⟨pkSeed, idealRoot vp prims g pkSeed⟩ R))
    (fun log m a => ?_) (fun m R => ?_)]
  · rfl
  · unfold itsrRandomizerO itsrRandomizer
    rcases hf : log.find? (fun e => decide (e.1 = m ∧ e.2.1 = a)) with _ | e
    · simp only [hf]
      exact simulateQ_tblImpl_gameQ g _
    · simp only [hf, simulateQ_pure]
  · exact openSign_tbl g m ⟨pkSeed, idealRoot vp prims g pkSeed⟩ R

/-! ## Same advantage -/

/-- The lazy and the eager ITSR adversary induce the same law of (candidate, targets). -/
theorem evalDist_bItsrL_run (A : Forger vp prims optRand pkSeedDist)
    [MeasurableSpace ((prims.Y × ItsrIn prims) ×
      KeyedHash.ITSRTranscript prims.Y (ItsrIn prims))] :
    𝒟[(bItsrL A).run] = 𝒟[(bItsr A).run] := by
  unfold KeyedHash.ITSRAdversary.run
  change 𝒟[(simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims))
    (lazyRun (PublicHash.impl prims) (itsrOpen A))).run []] = _
  rw [evalDist_lazyRun_eq_table (PublicHash.impl prims)
    (KeyedHash.ITSROracles (itsrProblem vp prims))
    (fun s => simulateQ_itsr_liftM_run _ s) (itsrOpen A)]
  simp only [itsrOpen_tbl, bItsr_main_eq, simulateQ_bind, StateT.run_bind,
    simulateQ_itsr_liftM_run, bind_map_left]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-- **Same advantage.** -/
theorem itsrAdvantage_bItsrL (A : Forger vp prims optRand pkSeedDist) :
    KeyedHash.ITSRAdvantage (bItsrL A) = KeyedHash.ITSRAdvantage (bItsr A) := by
  rw [KeyedHash.ITSRAdvantage_eq_evalDist_experiment,
    KeyedHash.ITSRAdvantage_eq_evalDist_experiment]
  let _ : MeasurableSpace ((prims.Y × ItsrIn prims) ×
      KeyedHash.ITSRTranscript prims.Y (ItsrIn prims)) := ⊤
  have hE : ∀ B : KeyedHash.ITSRAdversary (itsrProblem vp prims),
      KeyedHash.ITSRExperiment B =
        (fun z : (prims.Y × ItsrIn prims) × KeyedHash.ITSRTranscript prims.Y (ItsrIn prims) =>
          decide ((itsrProblem vp prims).Wins z.2 z.1)) <$> B.run := by
    intro B
    simp [KeyedHash.ITSRExperiment, map_eq_bind_pure_comp]
  rw [hE, hE, evalDist_map _ measurable_from_top, evalDist_map _ measurable_from_top,
    evalDist_bItsrL_run]

/-- **Step 4 with the lazy adversary.** -/
theorem stepITSR_lazy (A : Forger vp prims optRand pkSeedDist) : StepITSR A (bItsrL A) := by
  unfold StepITSR
  rw [itsrAdvantage_bItsrL]
  exact stepITSR A

/-! ## Resources -/

theorem itsrRandomizerO_kindBound (K : Kind) (pkSeed : prims.PkSeed) (root : prims.Y)
    (log : G2Log prims) (m : List Byte) (a : prims.Y) :
    IsQueryBoundP (itsrRandomizerO pkSeed root log m a) (fun t => kind t = K) (ind K .game) := by
  unfold itsrRandomizerO
  split
  · exact isQueryBoundP_pure _ _ _
  · exact gameQ_kindBound K _

/-- Queries of kind `K` (game / secret / hash) of the open program, for a forger with at most
`qs` signing queries. -/
theorem itsrOpen_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (itsrOpen A) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash) +
        qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))) := by
  have hrun : ∀ (pkSeed : prims.PkSeed) (root : prims.Y),
      IsQueryBoundP (runForgerLog A ⟨pkSeed, root⟩ (itsrRandomizerO pkSeed root)
          (fun m R => openSign prims (itsrG prims) m pkSeed root R)) (fun t => kind t = K)
        (qs * (ind K .game + signB vp (ind K .sec) (ind K .hash))) := by
    intro pkSeed root
    unfold runForgerLog
    refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
    · cases t with
      | inl n => simp at ht
      | inr m =>
        have hstep := qb_bind (fun t => kind t = K)
          (liftM_kindBound (gspec := itsrG prims) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK (optRand ⟨pkSeed, root⟩)) fun addrnd =>
          qb_bind (fun t => kind t = K)
            (itsrRandomizerO_kindBound K pkSeed root s m addrnd) fun R =>
            qb_bind (fun t => kind t = K) (m := 0)
              (openSign_kindBound (gspec := itsrG prims) K m pkSeed root R)
              fun sig => isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
        simpa [logSignOracle] using hstep
    · cases t with
      | inl n =>
        simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
        have h0 := qb_bind (fun t => kind t = K) (m := 0)
          (liftM_kindBound (gspec := itsrG prims) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK
            (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
        exact h0
      | inr m => simp at ht
  unfold itsrOpen
  exact (qb_bind _ (liftM_kindBound K hK pkSeedDist) fun pkSeed =>
    qb_bind _ (openKeygen_kindBound K pkSeed) fun root =>
      qb_bind _ (m := 0) (hrun _ _) fun z => isQueryBoundP_pure _ _ _).mono (by omega)

/-- `(bItsrL A).main` is the interpretation of the resource-explicit program
`lazyRes (itsrOpen A)` (fresh draw ↦ `$ᵗ prims.Y`, hash query ↦ evaluation). -/
theorem bItsrL_main_eq (A : Forger vp prims optRand pkSeedDist) :
    (bItsrL A).main = simulateQ (interp (PublicHash.impl prims)) (lazyRes (itsrOpen A)) := rfl

/-- (i) At most one ITSR target per signing query. -/
theorem bItsrL_queryBound (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bItsrL A).main (fun i => i.isRight = true) qs :=
  lazyRun_gameBound _ _ qs ((itsrOpen_kindBound A .game (by decide) qs hA).mono
    (by simp [ind, keygenB_game, signB_game]))

/-- (ii) Fresh uniform draws (= cache entries): at most `2^h'·len + qs·signReads`. -/
theorem bItsrL_draws (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (lazyRes (itsrOpen A)) (fun t => kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  lazyRes_bound_draws _ _ ((itsrOpen_kindBound A .sec (by decide) qs hA).mono
    (Nat.add_le_add keygenB_sec (Nat.mul_le_mul_left _ (by
      simpa [ind] using signB_sec (vp := vp)))))

/-- (iii) Hash evaluations: at most `keygenHashes + qs·signHashes`. -/
theorem bItsrL_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (lazyRes (itsrOpen A)) (fun t => kind t = .hash)
      (keygenHashes vp + qs * signHashes vp) :=
  lazyRes_bound_hash _ _ ((itsrOpen_kindBound A .hash (by decide) qs hA).mono
    (Nat.add_le_add keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [ind] using signB_hash (vp := vp)))))

/-- Game queries of the resource-explicit program. -/
theorem bItsrL_gameRes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (lazyRes (itsrOpen A)) (fun t => kind t = .game) qs :=
  lazyRes_bound_game _ _ ((itsrOpen_kindBound A .game (by decide) qs hA).mono
    (by simp [ind, keygenB_game, signB_game]))

end Lazy
end Reduction

#print axioms Reduction.Lazy.itsrAdvantage_bItsrL
#print axioms Reduction.Lazy.stepITSR_lazy
#print axioms Reduction.Lazy.bItsrL_queryBound
#print axioms Reduction.Lazy.bItsrL_draws
#print axioms Reduction.Lazy.bItsrL_hashes
