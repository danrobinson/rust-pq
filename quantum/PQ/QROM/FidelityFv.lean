import PQ.QROM.ExactFv
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity

/-!
# Final validity of the exact game and VCVio's sticky bit

The exact source-final-validity game (`PQ/QROM/ExactFv.lean`) records the two histories and
reads the final predicate `FvValid cap` in its winning condition.  VCVio's game
(`TweakableHash.SM_DT_TCR_SourceFinalValidity.experiment`) threads the monitor state
`SourceFinalValidity.State` with a sticky validity bit, updated by `State.recordTarget` and
`State.recordCollection`, and reads the bit.  This file proves that the two agree on every
state of the exact game:

* `fidFvMon cap s`: VCVio's monitor state of the histories `s`: the challenge history, the
  tweaks of the collection history, and the bit `decide (FvValid cap s)`.
* `fidFv_valid_iff`: `FvValid cap s ↔ SourceFinalValidity.Valid cap Prod.fst (fidFvMon cap s)`.
* `fidFv_invariant`: `fidFvMon cap s` satisfies VCVio's monitor invariant.
* `fidFv_step_inl`, `fidFv_step_inr`: one step of the exact challenger `fvCh` is one step of
  VCVio's monitor: `fidFvMon cap (fvCh a req s).2` is `recordTarget` / `recordCollection` of
  `fidFvMon cap s`.  Hence the bit `decide (FvValid cap ·)` IS the sticky bit along every run.
* `fidFv_chal_step`, `fidFv_coll_step`: VCVio's `challengeOracle` and
  `SourceFinalValidity.collectionOracle` for the problem `fidFvProblem cap Th` (hash
  `Th (P, (t, m))`, collection: the same function), run on `fidFvMon cap s`, return the answer
  and the state of `fvCh`.
* `fidFv_win_iff`: VCVio's final test on `fidFvMon cap s` returns `true` iff `fvWin` holds.
* `fidFv_reachable`: on every reachable state of VCVio's game, the sticky bit decides
  `SourceFinalValidity.Valid` (VCVio's `valid_eq_decide_valid_of_reachable`, cited).
-/

open OracleComp OracleSpec TweakableHash ENNReal

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type} [DecidableEq Tw]

open Classical in
/-- VCVio's monitor state for the histories of the exact game. -/
noncomputable def fidFvMon (cap : ℕ) (s : FvState Tw Msg) :
    SourceFinalValidity.State (Tw × Msg) Tw :=
  ⟨s.chal, s.coll.map Prod.fst, decide (FvValid cap s)⟩

/-- The final predicate of the exact game is VCVio's `SourceFinalValidity.Valid`. -/
theorem fidFv_valid_iff (cap : ℕ) (s : FvState Tw Msg) :
    FvValid cap s ↔ SourceFinalValidity.Valid cap Prod.fst (fidFvMon cap s) := by
  unfold FvValid SourceFinalValidity.Valid fidFvMon
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    rw [List.disjoint_right]
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    exact h p hp
  · intro h p hp hmem
    exact List.disjoint_right.1 h (List.mem_map.2 ⟨p, hp, rfl⟩) hmem

/-- The monitor state of the exact game satisfies VCVio's monitor invariant: its bit is the
executable check of the final predicate. -/
theorem fidFv_invariant (cap : ℕ) (s : FvState Tw Msg) :
    SourceFinalValidity.Invariant cap Prod.fst (fidFvMon cap s) := by
  unfold SourceFinalValidity.Invariant
  rw [Bool.eq_iff_iff, SourceFinalValidity.validBool_eq_true_iff, ← fidFv_valid_iff]
  simp [fidFvMon]

theorem fidFv_ext {cap : ℕ} {st st' : SourceFinalValidity.State (Tw × Msg) Tw}
    (h1 : st.challenges = st'.challenges) (h2 : st.collectionTweaks = st'.collectionTweaks)
    (hi : SourceFinalValidity.Invariant cap Prod.fst st)
    (hi' : SourceFinalValidity.Invariant cap Prod.fst st') : st = st' := by
  obtain ⟨c, t, v⟩ := st
  obtain ⟨c', t', v'⟩ := st'
  simp only at h1 h2
  subst h1 h2
  unfold SourceFinalValidity.Invariant at hi hi'
  simp only [SourceFinalValidity.validBool] at hi hi'
  rw [hi, hi']

/-- A target request of the exact game is `recordTarget` on the monitor. -/
theorem fidFv_step_inl (cap : ℕ) (a : Tw × Msg → Y) (tm : Tw × Msg) (s : FvState Tw Msg) :
    fidFvMon cap (fvCh a (.inl tm) s).2 = (fidFvMon cap s).recordTarget cap Prod.fst tm :=
  fidFv_ext rfl rfl (fidFv_invariant cap _)
    ((fidFv_invariant cap s).recordTarget cap Prod.fst _ tm)

/-- A collection request of the exact game is `recordCollection` on the monitor. -/
theorem fidFv_step_inr (cap : ℕ) (a : Tw × Msg → Y) (tm : Tw × Msg) (s : FvState Tw Msg) :
    fidFvMon cap (fvCh a (.inr tm) s).2 = (fidFvMon cap s).recordCollection Prod.fst tm.1 :=
  fidFv_ext (by simp [fidFvMon, fvCh, SourceFinalValidity.State.recordCollection])
    (by simp [fidFvMon, fvCh, SourceFinalValidity.State.recordCollection])
    (fidFv_invariant cap _) ((fidFv_invariant cap s).recordCollection cap Prod.fst _ tm.1)

/-- The initial state. -/
theorem fidFv_init (cap : ℕ) :
    fidFvMon cap (fvInit : FvState Tw Msg) = SourceFinalValidity.State.initial :=
  fidFv_ext rfl rfl (fidFv_invariant cap _) (SourceFinalValidity.invariant_initial _ _)

/-- VCVio's source-final-validity problem for the hash `Th`: seed uniform, the collection is
the same function, cap `cap`. -/
def fidFvProblem [SampleableType Sd] (cap : ℕ) (Th : Dom Sd Tw Msg → Y) :
    SM_DT_TCR_SourceFinalValidity.Problem Unit Sd Tw Msg Y where
  th := ⟨$ᵗ Sd, fun P t m ↦ Th (P, (t, m))⟩
  thColl := ⟨fun _ ↦ Msg, fun _ P t m ↦ Th (P, (t, m))⟩
  numTargets := cap

variable [SampleableType Sd]

/-- VCVio's target oracle, run on the monitor state of the exact game, is the challenger
`fvCh` of the exact game. -/
theorem fidFv_chal_step (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (tm : Tw × Msg)
    (s : FvState Tw Msg) :
    (SM_DT_TCR_SourceFinalValidity.challengeOracle (fidFvProblem cap Th) P tm).run
        (fidFvMon cap s) =
      pure ((fvCh (rowOf Th P) (.inl tm) s).1, fidFvMon cap (fvCh (rowOf Th P) (.inl tm) s).2) := by
  rw [fidFv_step_inl]
  exact SM_DT_TCR_SourceFinalValidity.challengeOracle_run

/-- VCVio's collection oracle, run on the monitor state of the exact game, is the challenger
`fvCh` of the exact game. -/
theorem fidFv_coll_step (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (q : (_ : Unit) × Tw × Msg) (s : FvState Tw Msg) :
    (SourceFinalValidity.collectionOracle (Q := Tw × Msg) Prod.fst (fidFvProblem cap Th).thColl
        P q).run (fidFvMon cap s) =
      pure ((fvCh (rowOf Th P) (.inr q.2) s).1,
        fidFvMon cap (fvCh (rowOf Th P) (.inr q.2) s).2) := by
  rw [fidFv_step_inr]
  exact SourceFinalValidity.collectionOracle_run _ _ _ _ _

/-- VCVio's final test of `SM_DT_TCR_SourceFinalValidity.experiment`, on the monitor state of
the exact game, is the winning condition `fvWin` of the exact game. -/
theorem fidFv_win_iff [DecidableEq Msg] [DecidableEq Y] (cap : ℕ) (Th : Dom Sd Tw Msg → Y)
    (P : Sd) (r : ℕ × Msg) (s : FvState Tw Msg) :
    (match (fidFvMon cap s).challenges[r.1]? with
      | none => false
      | some (t, mj) => (fidFvMon cap s).valid &&
          decide (r.2 ≠ mj ∧ (fidFvProblem cap Th).th.eval P t r.2 =
            (fidFvProblem cap Th).th.eval P t mj)) = true ↔
      fvWin cap (rowOf Th P) r s := by
  unfold fvWin
  rcases hg : s.chal[r.1]? with _ | ⟨t, mj⟩
  · simp [fidFvMon, hg]
  · simp only [fidFvMon, hg, fidFvProblem, rowOf, Bool.and_eq_true, decide_eq_true_iff]
    simp
    exact fun _ ↦ decide_eq_true_iff

/-- VCVio's run-level statement, cited: on every reachable state of VCVio's game the sticky
bit decides the final predicate. -/
theorem fidFv_reachable {prob : SM_DT_TCR_SourceFinalValidity.Problem Unit Sd Tw Msg Y}
    (adv : SM_DT_TCR_SourceFinalValidity.Adversary prob) (pk : Sd)
    {z : adv.State × SM_DT_TCR_SourceFinalValidity.State Tw Msg}
    (hz : z ∈ support ((simulateQ (SM_DT_TCR_SourceFinalValidity.oracles prob pk)
      adv.choose).run .initial)) :
    z.2.valid = decide (SourceFinalValidity.Valid prob.numTargets Prod.fst z.2) :=
  SM_DT_TCR_SourceFinalValidity.valid_eq_decide_valid_of_reachable adv pk hz

end PQ.QROM

#print axioms PQ.QROM.fidFv_valid_iff
#print axioms PQ.QROM.fidFv_invariant
#print axioms PQ.QROM.fidFv_step_inl
#print axioms PQ.QROM.fidFv_step_inr
#print axioms PQ.QROM.fidFv_chal_step
#print axioms PQ.QROM.fidFv_coll_step
#print axioms PQ.QROM.fidFv_win_iff
#print axioms PQ.QROM.fidFv_reachable
