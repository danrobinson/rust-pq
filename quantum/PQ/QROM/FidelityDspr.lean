import PQ.QROM.FidelityFvExp
import PQ.QROM.ExactDsprClosed
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity

/-!
# Fidelity of the exact SM-DT-DSPR (source final validity) games

`dsprSucc` / `dsprSP` (`PQ/QROM/ExactUd.lean`), restricted to classical adversaries with one
uniform coin, are VCVio's `SM_DT_DSPR_SourceFinalValidity.Success` / `SPProbability` at a
uniformly random tweakable hash, for the problem `fidDsprProblem cap Th` (collection: the same
function).

* `fid_dspr_run`: VCVio's first phase is the classical run against the challenger `fvCh`.
* `fid_dspr_succ_eq`, `fid_dspr_sp_eq`: the two fidelity equalities.
* `fid_dspr_classical_le`: `dspr_exact_adv_le` for the averaged probabilities:
  `avg_Th Success − avg_Th SPProbability ≤ …`.  (This is the difference of the averages; VCVio's
  `advantage` is the truncated difference per hash, whose average can be larger.)
-/

open OracleComp OracleSpec TweakableHash ENNReal Quantum Matrix

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Sd Tw Msg Ω : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [SampleableType Sd] [Fintype Ω] [Nonempty Ω] [SampleableType Ω]

/-- VCVio's source-final-validity DSPR problem for the hash `Th`. -/
def fidDsprProblem (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    SM_DT_DSPR_SourceFinalValidity.Problem Unit Sd Tw Msg Y where
  th := ⟨$ᵗ Sd, fun P t m ↦ Th (P, (t, m))⟩
  thColl := ⟨fun _ ↦ Msg, fun _ P t m ↦ Th (P, (t, m))⟩
  numTargets := cap

/-- A classical DSPR adversary with a uniform coin drawn at the start. -/
structure FidDsprAdv (Ω Sd Tw Msg Y : Type) where
  /-- Private state carried from `choose` to `guess`. -/
  State : Type
  /-- The first phase, for the coin `ω`. -/
  choose : Ω → OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidFvReqSpec Tw Msg Y) State
  /-- The second phase. -/
  guess : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) (ℕ × Bool)

/-- Answer hash queries with `Th`; pass challenge and collection queries on. -/
def fidDsprInst (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    QueryImpl ((Dom Sd Tw Msg →ₒ Y) + fidFvReqSpec Tw Msg Y) (OracleComp (unifSpec +
      (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidDsprProblem cap Th).thColl))) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => liftM (OracleSpec.query (spec := unifSpec +
      (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidDsprProblem cap Th).thColl)) (.inr r))

/-- VCVio's adversary at the hash `Th`. -/
noncomputable def FidDsprAdv.honest (cap : ℕ) (A : FidDsprAdv Ω Sd Tw Msg Y)
    (Th : Dom Sd Tw Msg → Y) :
    SM_DT_DSPR_SourceFinalValidity.Adversary (fidDsprProblem cap Th) where
  State := A.State
  choose := do
    let ω ← (liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (unifSpec +
      (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidDsprProblem cap Th).thColl)) Ω)
    simulateQ (fidDsprInst cap Th) (A.choose ω)
  guess st P := simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.guess st P)

theorem fid_dspr_chal_step (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (tm : Tw × Msg)
    (s : FvState Tw Msg) :
    (SM_DT_DSPR_SourceFinalValidity.challengeOracle (fidDsprProblem cap Th) P tm).run
        (fidFvMon cap s) =
      pure ((fvCh (rowOf Th P) (.inl tm) s).1, fidFvMon cap (fvCh (rowOf Th P) (.inl tm) s).2) := by
  rw [fidFv_step_inl]
  exact SM_DT_DSPR_SourceFinalValidity.challengeOracle_run

/-- VCVio's first phase, with hash queries answered by `Th`, is the classical run against the
challenger `fvCh` of the exact game. -/
theorem fid_dspr_run (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) {State : Type}
    (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidFvReqSpec Tw Msg Y) State) (s : FvState Tw Msg) :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (fidDsprProblem cap Th) P)
        (simulateQ (fidDsprInst cap Th) oa)).run (fidFvMon cap s) =
      pure ((fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) oa s).1,
        fidFvMon cap (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) oa s).2) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with q | tm | q
    · simp only [fidDsprInst]
      rw [pure_bind]
      exact ih (Th q) s
    · simp only [fidDsprInst]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine Eq.trans (congrArg (· >>= _) (fid_dspr_chal_step cap Th P tm s)) ?_
      rw [pure_bind]
      exact ih _ _
    · simp only [fidDsprInst]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine Eq.trans (congrArg (· >>= _) (fidFv_coll_step cap Th P q s)) ?_
      rw [pure_bind]
      exact ih _ _

/-- The rest of VCVio's experiments after the seed `P` and the coin `ω` are drawn, with the
final test `Q t m b` on the selected target `(t, m)` and the guessed bit `b`. -/
noncomputable def fidDsprRest (Q : Sd → Tw → Msg → Bool → Bool) (cap : ℕ)
    (Th : Dom Sd Tw Msg → Y) (A : FidDsprAdv Ω Sd Tw Msg Y) (P : Sd) (ω : Ω) : ProbComp Bool := do
  let (privateState, gameState) ←
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (fidDsprProblem cap Th) P)
      (simulateQ (fidDsprInst cap Th) (A.choose ω))).run .initial
  let (j, b) ← simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.guess privateState P)
  match gameState.challenges[j]? with
  | none => return false
  | some (t, m) => return gameState.valid && Q P t m b

theorem fid_dspr_run_lift {α : Type} (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (oa : ProbComp α) (s : SM_DT_DSPR_SourceFinalValidity.State Tw Msg) :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (fidDsprProblem cap Th) P)
      (liftM oa : OracleComp (unifSpec +
      (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidDsprProblem cap Th).thColl)) α)).run s =
      oa >>= fun a ↦ pure (a, s) := by
  unfold SM_DT_DSPR_SourceFinalValidity.oracles
  rw [QueryImpl.simulateQ_add_liftM_left]
  simp

theorem fid_dspr_experiment (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidDsprAdv Ω Sd Tw Msg Y) :
    SM_DT_DSPR_SourceFinalValidity.experiment (A.honest cap Th) =
      (do let P ← $ᵗ Sd; let ω ← $ᵗ Ω
          fidDsprRest (fun P t m b ↦ decide (SecondPreimageExists (fidDsprProblem cap Th).th P t m ↔
            b = true)) cap Th A P ω : ProbComp Bool) := by
  unfold SM_DT_DSPR_SourceFinalValidity.experiment
  refine bind_congr (m := ProbComp) fun P ↦ ?_
  simp only [FidDsprAdv.honest]
  rw [simulateQ_bind, StateT.run_bind, fid_dspr_run_lift]
  simp only [bind_assoc, pure_bind]
  rfl

theorem fid_dspr_spExperiment (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidDsprAdv Ω Sd Tw Msg Y) :
    SM_DT_DSPR_SourceFinalValidity.spExperiment (A.honest cap Th) =
      (do let P ← $ᵗ Sd; let ω ← $ᵗ Ω
          fidDsprRest (fun P t m _ ↦ decide (SecondPreimageExists (fidDsprProblem cap Th).th P t m))
            cap Th A P ω : ProbComp Bool) := by
  unfold SM_DT_DSPR_SourceFinalValidity.spExperiment
  refine bind_congr (m := ProbComp) fun P ↦ ?_
  simp only [FidDsprAdv.honest]
  rw [simulateQ_bind, StateT.run_bind, fid_dspr_run_lift]
  simp only [bind_assoc, pure_bind]
  rfl

/-- The rest of VCVio's experiment is the win of the classical run in the exact game, for a
final test `Q` that decides the predicate `W` of the row. -/
theorem fid_dspr_rest (Q : Sd → Tw → Msg → Bool → Bool)
    (W : (Tw × Msg → Y) → Tw → Msg → Bool → Prop) (cap : ℕ) (Th : Dom Sd Tw Msg → Y)
    (A : FidDsprAdv Ω Sd Tw Msg Y) (P : Sd) (ω : Ω)
    (hQ : ∀ t m b, Q P t m b = true ↔ W (rowOf Th P) t m b) :
    fidPr (fidDsprRest Q cap Th A P ω) =
      ind (FvValid cap (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).2 ∧
        ∃ t m, (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).2.chal[
          (evalWithAnswerFn (QueryImpl.ofFn Th) (A.guess
            (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).1 P)).1]? =
            some (t, m) ∧
          W (rowOf Th P) t m (evalWithAnswerFn (QueryImpl.ofFn Th) (A.guess
            (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).1 P)).2) := by
  have h := fid_dspr_run cap Th P (A.choose ω) fvInit
  rw [fidFv_init] at h
  unfold fidDsprRest
  rw [h, pure_bind]
  simp only
  rw [fid_simulateQ_pure, pure_bind]
  set r := evalWithAnswerFn (QueryImpl.ofFn Th)
    (A.guess (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).1 P)
  set s := (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).2
  have hch : (fidFvMon cap s).challenges = s.chal := rfl
  have hv : (fidFvMon cap s).valid = true ↔ FvValid cap s := by simp [fidFvMon]
  simp only [hch]
  rcases hg : s.chal[r.1]? with _ | ⟨t, m⟩
  · rw [fidPr_pure, ind_of_false (by simp), ind_of_false (by simp)]
  · rw [fidPr_pure]
    by_cases hc : FvValid cap s ∧ W (rowOf Th P) t m r.2
    · exact (ind_of_true (Bool.and_eq_true_iff.2 ⟨hv.2 hc.1, (hQ t m r.2).2 hc.2⟩)).trans
        (ind_of_true ⟨hc.1, t, m, rfl, hc.2⟩).symm
    · refine (ind_of_false fun hb ↦ ?_).trans (ind_of_false ?_).symm
      · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hb
        exact hc ⟨hv.1 h1, (hQ t m r.2).1 h2⟩
      · rintro ⟨h1, t', m', ht', hw⟩
        cases Option.some.inj ht'
        exact hc ⟨h1, hw⟩

theorem fid_dspr_generic (Q : (Dom Sd Tw Msg → Y) → Sd → Tw → Msg → Bool → Bool)
    (W : (Tw × Msg → Y) → Tw → Msg → Bool → Prop)
    (hQ : ∀ Th P t m b, Q Th P t m b = true ↔ W (rowOf Th P) t m b)
    (cap : ℕ) (A : FidDsprAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n) :
    twoPhaseExp .instruments (A := QReg.of Unit) (SubState.basis ()) fvCh fvInit n
        (fidGCoinEmb (fidFvCodec Tw Msg Y) A.choose n) (fidGPh2 A.guess)
        (fun a r s ↦ FvValid cap s ∧ ∃ t m, s.chal[r.1]? = some (t, m) ∧ W a t m r.2) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ fidPr (do
        let P ← $ᵗ Sd
        let ω ← $ᵗ Ω
        fidDsprRest (Q Th) cap Th A P ω) := by
  rw [fidGCoin_twoPhaseExp]
  unfold twoPhaseExp
  rw [avg_comm, avg_congr fun P ↦ avg_comm _, avg_comm]
  refine avg_congr fun Th ↦ ?_
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun P ↦ ?_
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun ω ↦ ?_
  rw [fid_dspr_rest (Q Th) W cap Th A P ω (hQ Th P), fidG_realProb _ _ _ _ _ _ _ (hb ω)]

/-- **Fidelity of the exact DSPR success probability.** -/
theorem fid_dspr_succ_eq (cap : ℕ) (A : FidDsprAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n) :
    dsprSucc .instruments (A := QReg.of Unit) (SubState.basis ()) cap n
        (fidGCoinEmb (fidFvCodec Tw Msg Y) A.choose n) (fidGPh2 A.guess) =
      avg fun Th : Dom Sd Tw Msg → Y ↦
        SM_DT_DSPR_SourceFinalValidity.Success (A.honest cap Th) := by
  unfold SM_DT_DSPR_SourceFinalValidity.Success
  simp only [fid_dspr_experiment]
  exact fid_dspr_generic
    (fun Th P t m b ↦ decide (SecondPreimageExists (fidDsprProblem cap Th).th P t m ↔ b = true))
    (fun a t m b ↦ HasSecondPreimage a t m ↔ b = true)
    (fun Th P t m b ↦ decide_eq_true_iff) cap A n hb

/-- **Fidelity of the exact `SPprob` baseline.** -/
theorem fid_dspr_sp_eq (cap : ℕ) (A : FidDsprAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n) :
    dsprSP .instruments (A := QReg.of Unit) (SubState.basis ()) cap n
        (fidGCoinEmb (fidFvCodec Tw Msg Y) A.choose n) (fidGPh2 A.guess) =
      avg fun Th : Dom Sd Tw Msg → Y ↦
        SM_DT_DSPR_SourceFinalValidity.SPProbability (A.honest cap Th) := by
  unfold SM_DT_DSPR_SourceFinalValidity.SPProbability
  simp only [fid_dspr_spExperiment]
  exact fid_dspr_generic
    (fun Th P t m _ ↦ decide (SecondPreimageExists (fidDsprProblem cap Th).th P t m))
    (fun a t m _ ↦ HasSecondPreimage a t m)
    (fun Th P t m b ↦ decide_eq_true_iff) cap A n hb

/-- **The exact DSPR bound for VCVio's probabilities**, averaged over the uniformly random
tweakable hash. -/
theorem fid_dspr_classical_le [Inhabited Tw] [Nonempty Msg] [Nontrivial Y] (cap : ℕ)
    (A : FidDsprAdv Ω Sd Tw Msg Y) (n q₁ q₂ : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n)
    (h1 : ∀ ω, IsQueryBoundP (A.choose ω) fidIsHash q₁)
    (h2 : ∀ st P, IsTotalQueryBound (A.guess st P) q₂) :
    (avg fun Th : Dom Sd Tw Msg → Y ↦
        SM_DT_DSPR_SourceFinalValidity.Success (A.honest cap Th)) -
      (avg fun Th : Dom Sd Tw Msg → Y ↦
        SM_DT_DSPR_SourceFinalValidity.SPProbability (A.honest cap Th)) ≤
      (dsprTrivial Msg Y + 8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) +
        2 * seedLoss Sd q₁ := by
  rw [← fid_dspr_succ_eq cap A n hb, ← fid_dspr_sp_eq cap A n hb]
  exact dspr_exact_adv_le (fidGCoin_emb_isQueryBound _ A.choose n q₁ h1)
    (fidG_ph2_isQueryBound A.guess q₂ h2)

end PQ.QROM

#print axioms PQ.QROM.fid_dspr_run
#print axioms PQ.QROM.fid_dspr_succ_eq
#print axioms PQ.QROM.fid_dspr_sp_eq
#print axioms PQ.QROM.fid_dspr_classical_le
