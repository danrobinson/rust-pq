import PQ.QROM.FidelityGen
import PQ.QROM.FidelityFv

/-!
# Fidelity of the exact source-final-validity SM-DT-TCR game

`tcrFvExp` (`PQ/QROM/ExactFv.lean`), restricted to classical adversaries that draw one uniform
coin at the start and reach the hash through classical queries, is VCVio's
`SM_DT_TCR_SourceFinalValidity.advantage` at a uniformly random tweakable hash.

* `FidFvAdv Ω Sd Tw Msg Y`: `choose : Ω → OracleComp (hash + (challenge + collection)) State`,
  `forge : State → Sd → OracleComp hash (ℕ × Msg)`; the oracles are the always-answering ones
  of the source-final-validity game.  (`Ω = Unit` is the coin-free case.)
* `FidFvAdv.honest cap A Th`: VCVio's adversary for `fidFvProblem cap Th`: sample `ω ← $ᵗ Ω`,
  run `A.choose ω` with hash queries answered by `Th`.
* `fid_fv_tcrFvExp_eq`: `tcrFvExp (embedding) = avg_Th advantage (A.honest cap Th)`.
* `fid_fv_classical_le`: `tcr_fv_exact_le` as a bound on VCVio's advantage.
-/

open OracleComp OracleSpec TweakableHash ENNReal Quantum Matrix

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Sd Tw Msg Ω : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [SampleableType Sd] [Fintype Ω] [Nonempty Ω] [SampleableType Ω]

/-- The collection oracle's signature of the source-final-validity game, one-member collection. -/
abbrev fidFvCollSpec (Tw Msg Y : Type) : OracleSpec ((_ : Unit) × Tw × Msg) := _ →ₒ Y

/-- The request oracles of the source-final-validity game: target oracle, collection oracle. -/
abbrev fidFvReqSpec (Tw Msg Y : Type) :=
  SM_DT_TCR_SourceFinalValidity.challengeSpec Tw Msg Y + fidFvCollSpec Tw Msg Y

/-- Requests of the exact game for the queries of the two oracles. -/
def fidFvCodec (Tw Msg Y : Type) [AddCommGroup Y] :
    FidCodec (fidFvReqSpec Tw Msg Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y where
  enc r := match r with
    | .inl tm => .inl tm
    | .inr q => .inr q.2
  dec r y := match r with
    | .inl _ => y
    | .inr _ => y
  dflt r := match r with
    | .inl _ => (0 : Y)
    | .inr _ => (0 : Y)

/-- A classical source-final-validity adversary with a uniform coin drawn at the start. -/
structure FidFvAdv (Ω Sd Tw Msg Y : Type) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- The first phase, for the coin `ω`. -/
  choose : Ω → OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidFvReqSpec Tw Msg Y) State
  /-- The second phase. -/
  forge : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) (ℕ × Msg)

/-- Answer hash queries with `Th`; pass target and collection queries on. -/
def fidFvInst (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    QueryImpl ((Dom Sd Tw Msg →ₒ Y) + fidFvReqSpec Tw Msg Y) (OracleComp (unifSpec +
      (SM_DT_TCR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidFvProblem cap Th).thColl))) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => liftM (OracleSpec.query (spec := unifSpec +
      (SM_DT_TCR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidFvProblem cap Th).thColl)) (.inr r))

/-- VCVio's adversary at the hash `Th`. -/
noncomputable def FidFvAdv.honest (cap : ℕ) (A : FidFvAdv Ω Sd Tw Msg Y)
    (Th : Dom Sd Tw Msg → Y) : SM_DT_TCR_SourceFinalValidity.Adversary (fidFvProblem cap Th) where
  State := A.State
  choose := do
    let ω ← (liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (unifSpec +
      (SM_DT_TCR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidFvProblem cap Th).thColl)) Ω)
    simulateQ (fidFvInst cap Th) (A.choose ω)
  forge st P := simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.forge st P)

/-- VCVio's first phase, with hash queries answered by `Th`, is the classical run against the
challenger `fvCh` of the exact game. -/
theorem fid_fv_run (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) {State : Type}
    (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidFvReqSpec Tw Msg Y) State) (s : FvState Tw Msg) :
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fidFvProblem cap Th) P)
        (simulateQ (fidFvInst cap Th) oa)).run (fidFvMon cap s) =
      pure ((fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) oa s).1,
        fidFvMon cap (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) oa s).2) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with q | tm | q
    · simp only [fidFvInst]
      rw [pure_bind]
      exact ih (Th q) s
    · simp only [fidFvInst]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine Eq.trans (congrArg (· >>= _) (fidFv_chal_step cap Th P tm s)) ?_
      rw [pure_bind]
      exact ih _ _
    · simp only [fidFvInst]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine Eq.trans (congrArg (· >>= _) (fidFv_coll_step cap Th P q s)) ?_
      rw [pure_bind]
      exact ih _ _

/-- The rest of VCVio's experiment after the seed `P` and the coin `ω` are drawn. -/
noncomputable def fidFvRest (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidFvAdv Ω Sd Tw Msg Y)
    (P : Sd) (ω : Ω) : ProbComp Bool := do
  let (privateState, gameState) ←
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fidFvProblem cap Th) P)
      (simulateQ (fidFvInst cap Th) (A.choose ω))).run .initial
  let (j, m) ← simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.forge privateState P)
  match gameState.challenges[j]? with
  | none => return false
  | some (t, mj) =>
      return gameState.valid && decide (m ≠ mj ∧
        (fidFvProblem cap Th).th.eval P t m = (fidFvProblem cap Th).th.eval P t mj)

theorem fid_fv_run_lift {α : Type} (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (oa : ProbComp α)
    (s : SM_DT_TCR_SourceFinalValidity.State Tw Msg) :
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (fidFvProblem cap Th) P)
      (liftM oa : OracleComp (unifSpec +
      (SM_DT_TCR_SourceFinalValidity.challengeSpec Tw Msg Y +
        SourceFinalValidity.collectionSpec (fidFvProblem cap Th).thColl)) α)).run s =
      oa >>= fun a ↦ pure (a, s) := by
  unfold SM_DT_TCR_SourceFinalValidity.oracles
  rw [QueryImpl.simulateQ_add_liftM_left]
  simp

theorem fid_fv_experiment (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidFvAdv Ω Sd Tw Msg Y) :
    SM_DT_TCR_SourceFinalValidity.experiment (A.honest cap Th) =
      (do let P ← $ᵗ Sd; let ω ← $ᵗ Ω; fidFvRest cap Th A P ω : ProbComp Bool) := by
  unfold SM_DT_TCR_SourceFinalValidity.experiment
  refine bind_congr (m := ProbComp) fun P ↦ ?_
  simp only [FidFvAdv.honest]
  rw [simulateQ_bind, StateT.run_bind, fid_fv_run_lift]
  simp only [bind_assoc, pure_bind]
  rfl

open Classical in
/-- The rest of VCVio's experiment is the win of the classical run in the exact game. -/
theorem fid_fv_rest (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidFvAdv Ω Sd Tw Msg Y)
    (P : Sd) (ω : Ω) :
    fidPr (fidFvRest cap Th A P ω) =
      ind (fvWin cap (rowOf Th P)
        (evalWithAnswerFn (QueryImpl.ofFn Th)
          (A.forge (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).1 P))
        (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).2) := by
  have h := fid_fv_run cap Th P (A.choose ω) fvInit
  rw [fidFv_init] at h
  unfold fidFvRest
  rw [h, pure_bind]
  simp only
  rw [fid_simulateQ_pure, pure_bind]
  set r := evalWithAnswerFn (QueryImpl.ofFn Th)
    (A.forge (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).1 P)
  set s := (fidGRun (fidFvCodec Tw Msg Y) Th (fvCh (rowOf Th P)) (A.choose ω) fvInit).2
  have hw := fidFv_win_iff cap Th P r s
  rcases hg : (fidFvMon cap s).challenges[r.1]? with _ | ⟨t, mj⟩
  · rw [hg] at hw
    rw [fidPr_pure, ind_of_false (by simp), ind_of_false (fun hc ↦ by simpa using hw.2 hc)]
  · rw [hg] at hw
    simp only at hw
    rw [fidPr_pure]
    by_cases hc : fvWin cap (rowOf Th P) r s
    · rw [ind_of_true hc, ind_of_true (hw.2 hc)]
    · rw [ind_of_false hc, ind_of_false (fun h' ↦ hc (hw.1 h'))]

/-- **Fidelity of the exact source-final-validity SM-DT-TCR game.** -/
theorem fid_fv_tcrFvExp_eq (cap : ℕ) (A : FidFvAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n) :
    tcrFvExp .instruments (A := QReg.of Unit) (SubState.basis ()) cap n
        (fidGCoinEmb (fidFvCodec Tw Msg Y) A.choose n) (fidGPh2 A.forge) =
      avg fun Th : Dom Sd Tw Msg → Y ↦
        SM_DT_TCR_SourceFinalValidity.advantage (A.honest cap Th) := by
  unfold tcrFvExp SM_DT_TCR_SourceFinalValidity.advantage
  rw [fidGCoin_twoPhaseExp]
  unfold twoPhaseExp
  rw [avg_comm, avg_congr fun P ↦ avg_comm _, avg_comm]
  refine avg_congr fun Th ↦ ?_
  rw [fid_fv_experiment]
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun P ↦ ?_
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun ω ↦ ?_
  rw [fid_fv_rest, fidG_realProb _ _ _ _ _ _ _ (hb ω)]

/-- **`tcr_fv_exact_le` as a bound on VCVio's source-final-validity advantage**, averaged over
the uniformly random tweakable hash. -/
theorem fid_fv_classical_le [Inhabited Tw] (cap : ℕ) (A : FidFvAdv Ω Sd Tw Msg Y) (n q₁ q₂ : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n)
    (h1 : ∀ ω, IsQueryBoundP (A.choose ω) fidIsHash q₁)
    (h2 : ∀ st P, IsTotalQueryBound (A.forge st P) q₂) :
    (avg fun Th : Dom Sd Tw Msg → Y ↦
        SM_DT_TCR_SourceFinalValidity.advantage (A.honest cap Th)) ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [← fid_fv_tcrFvExp_eq cap A n hb]
  exact tcr_fv_exact_le (fidGCoin_emb_isQueryBound _ A.choose n q₁ h1)
    (fidG_ph2_isQueryBound A.forge q₂ h2)

end PQ.QROM

#print axioms PQ.QROM.fid_fv_run
#print axioms PQ.QROM.fid_fv_tcrFvExp_eq
#print axioms PQ.QROM.fid_fv_classical_le
