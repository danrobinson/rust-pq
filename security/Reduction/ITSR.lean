import Reduction.Harness

/-!
# Steps 3 and 4: the case split and the ITSR branch

`stepSplit`: `classify` is total, so the success event of `G2` is the disjoint union of the four
class events.

`bItsr A` (EC: `R_ITSR_EUFCMA`) samples `PK.seed` and (as written) the eager `2^256`-cell table
— infeasible; `Reduction.Lazy.bItsrL` samples the cells lazily —, runs `A` once in the shape of
`G2`, obtaining each *fresh* randomizer from the ITSR target oracle on `(PK.seed, PK.root, M)` and
reusing the recorded randomizer on a repeated `(opt_rand, M)`; it outputs the forgery's
`(R*, (PK.seed, PK.root, M*))`.  If the forgery is fresh its pair is not a target, and class
`itsr` is exactly the covering condition of `ITSRProblem.Wins`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## Probability bookkeeping -/

/-- Success probability of `mx >>= pure ∘ b` as an event probability. -/
theorem prTrue_bind_pure {α : Type} (mx : ProbComp α) (b : α → Bool) :
    prTrue (mx >>= fun z => pure (b z)) = Pr{let z ← mx}[b z = true] := by
  rw [prEvent_eq_evalDist_decide]
  simp [prTrue]

/-- The joint sample space of `G2`: seed, table, forgery and transcript. -/
noncomputable def g2Joint (A : Forger vp prims optRand pkSeedDist) :
    ProbComp (prims.PkSeed × SecretTable vp prims ×
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims)) := do
  let pkSeed ← pkSeedDist
  let tbl ← sampleTable vp prims
  let z ← g2Run A tbl (idealPk vp prims tbl pkSeed)
  return (pkSeed, tbl, z)

theorem g2_eq_joint (A : Forger vp prims optRand pkSeedDist) :
    g2 A = g2Joint A >>= fun w =>
      pure (g2Valid (idealPk vp prims w.2.1 w.1) w.2.2.2 w.2.2.1.1 w.2.2.1.2) := by
  simp [g2, g2Joint]

theorem g2Class_eq_joint (A : Forger vp prims optRand pkSeedDist) (c : ForgeryClass) :
    g2Class A c = g2Joint A >>= fun w =>
      pure (g2Valid (idealPk vp prims w.2.1 w.1) w.2.2.2 w.2.2.1.1 w.2.2.1.2 &&
        decide (g2ClassOf w.2.1 (idealPk vp prims w.2.1 w.1) w.2.2.2 w.2.2.1.1 w.2.2.1.2 = c)) := by
  simp [g2Class, g2Joint]

/-- **Step 3.** -/
theorem stepSplit (A : Forger vp prims optRand pkSeedDist) : StepSplit A := by
  unfold StepSplit
  rw [g2_eq_joint, g2Class_eq_joint, g2Class_eq_joint, g2Class_eq_joint, g2Class_eq_joint]
  simp only [prTrue_bind_pure]
  refine le_trans ?_ (add_le_add (add_le_add (prEvent_or_le _ _ _) le_rfl) le_rfl)
  refine le_trans ?_ (add_le_add (prEvent_or_le _ _ _) le_rfl)
  refine le_trans ?_ (prEvent_or_le _ _ _)
  refine prEvent_mono _ _ _ fun w hw => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, hw, true_and]
  cases g2ClassOf w.2.1 (idealPk vp prims w.2.1 w.1) w.2.2.2 w.2.2.1.1 w.2.2.1.2 <;> simp

/-! ## The ITSR reduction -/

/-- Input type of the ITSR instance: `(PK.seed, PK.root, M)`. -/
abbrev ItsrIn (prims : Primitives vp.params) : Type := prims.PkSeed × prims.Y × List Byte

/-- Oracle interface of an ITSR adversary. -/
abbrev itsrSpec (prims : Primitives vp.params) : OracleSpec (ℕ ⊕ ItsrIn prims) :=
  unifSpec + KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y

/-- The randomizer of `bItsr`: reuse the recorded value on a repeated `(opt_rand, M)`, otherwise
ask for a fresh ITSR target on `(PK.seed, PK.root, M)`. -/
def itsrRandomizer (pkSeed : prims.PkSeed) (root : prims.Y) (log : G2Log prims) (m : List Byte)
    (addrnd : prims.Y) : OracleComp (itsrSpec prims) prims.Y :=
  match log.find? (fun e => decide (e.1 = m ∧ e.2.1 = addrnd)) with
  | some e => pure e.2.2
  | none => ((itsrSpec prims).query (Sum.inr (pkSeed, root, m)) :
      OracleComp (itsrSpec prims) prims.Y)

/-- The ITSR adversary built from a forger. -/
noncomputable def bItsr (A : Forger vp prims optRand pkSeedDist) :
    KeyedHash.ITSRAdversary (itsrProblem vp prims) where
  main := do
    let pkSeed ← (monadLift pkSeedDist : OracleComp (itsrSpec prims) prims.PkSeed)
    let tbl ← (monadLift (sampleTable vp prims) :
      OracleComp (itsrSpec prims) (SecretTable vp prims))
    let pk := idealPk vp prims tbl pkSeed
    let z ← runForgerLog A pk (itsrRandomizer pkSeed pk.pkRoot)
      (fun m R => pure (idealSign vp prims tbl m pk R))
    return (z.1.2.randomness, (pkSeed, pk.pkRoot, z.1.1))

/-! ### The target transcript as a function of the `G2` transcript -/

section Targets

variable (pkSeed : prims.PkSeed) (root : prims.Y)

/-- Targets issued along a transcript given newest-first. -/
def targetsRev : G2Log prims → KeyedHash.ITSRTranscript prims.Y (ItsrIn prims)
  | [] => []
  | e :: older => targetsRev older ++
      (match older.reverse.find? (fun e' => decide (e'.1 = e.1 ∧ e'.2.1 = e.2.1)) with
       | some _ => []
       | none => [(e.2.2, (pkSeed, root, e.1))])

/-- The ITSR targets `bItsr` has issued when its transcript is `log`: one per entry whose
`(M, opt_rand)` did not occur earlier. -/
def targetsOf (log : G2Log prims) : KeyedHash.ITSRTranscript prims.Y (ItsrIn prims) :=
  targetsRev pkSeed root log.reverse

theorem targetsOf_nil : targetsOf pkSeed root ([] : G2Log prims) = [] := rfl

theorem targetsOf_append (log : G2Log prims) (e : List Byte × prims.Y × prims.Y) :
    targetsOf pkSeed root (log ++ [e]) = targetsOf pkSeed root log ++
      (match log.find? (fun e' => decide (e'.1 = e.1 ∧ e'.2.1 = e.2.1)) with
       | some _ => []
       | none => [(e.2.2, (pkSeed, root, e.1))]) := by
  simp [targetsOf, targetsRev]

/-- Every target comes from a transcript entry. -/
theorem mem_targetsOf (log : G2Log prims) (x : prims.Y × ItsrIn prims)
    (hx : x ∈ targetsOf pkSeed root log) :
    ∃ e ∈ log, x = (e.2.2, (pkSeed, root, e.1)) := by
  induction log using List.reverseRecOn with
  | nil => simp [targetsOf_nil] at hx
  | append_singleton log e ih =>
    rw [targetsOf_append, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨e', he', rfl⟩ := ih hx
      exact ⟨e', by simp [he'], rfl⟩
    · split at hx
      · simp at hx
      · exact ⟨e, by simp, by simpa using hx⟩

/-- Transcript invariant: every entry's `(R, (PK.seed, PK.root, M))` is a target. -/
def LogCovered (log : G2Log prims) : Prop :=
  ∀ e ∈ log, (e.2.2, (pkSeed, root, e.1)) ∈ targetsOf pkSeed root log

end Targets

/-! ### Simulation: `bItsr` inside the ITSR game is `G2` -/

section Sim

variable (pkSeed : prims.PkSeed) (root : prims.Y) (pk : PublicKeyCore prims.core)
  (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core)

/-- The handler `bItsr` runs the forger against. -/
noncomputable abbrev implB :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (itsrSpec prims))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (itsrSpec prims))).liftTarget
      (StateT (G2Log prims) (OracleComp (itsrSpec prims))) +
    logSignOracle optRand pk (itsrRandomizer pkSeed root) (fun m R => pure (signR m R))

/-- The handler of `G2`. -/
noncomputable abbrev implG :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
    g2SignOracle optRand pk signR

theorem simulateQ_itsr_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims))
      (liftM oa : OracleComp (itsrSpec prims) α) = liftM oa := by
  simp [KeyedHash.ITSROracles, QueryImpl.simulateQ_add_liftM_left]

theorem simulateQ_itsr_liftM_run {α : Type} (oa : ProbComp α)
    (tg : KeyedHash.ITSRTranscript prims.Y (ItsrIn prims)) :
    (simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims))
      (liftM oa : OracleComp (itsrSpec prims) α)).run tg = (fun a => (a, tg)) <$> oa := by
  rw [simulateQ_itsr_liftM]
  simp

theorem sim_step (t : ℕ ⊕ List Byte) (log : G2Log prims) :
    (simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims))
        ((implB (optRand := optRand) pkSeed root pk signR t).run log)).run
        (targetsOf pkSeed root log) =
      (fun z => (z, targetsOf pkSeed root z.2)) <$>
        (implG (optRand := optRand) pk signR t).run log := by
  rcases t with n | msg
  · have h := simulateQ_itsr_liftM_run (vp := vp) (prims := prims)
      (liftM (unifSpec.query n) : ProbComp _) (targetsOf pkSeed root log)
    simp [implB, implG]
    erw [h]
    simp
  · simp only [implB, implG, logSignOracle, g2SignOracle, QueryImpl.add_apply_inr]
    simp
    erw [simulateQ_itsr_liftM_run]
    simp only [bind_map_left]
    refine bind_congr fun addrnd => ?_
    unfold itsrRandomizer lazyRandomizer
    simp only [targetsOf_append]
    rcases hf : log.find? (fun e => decide (e.1 = msg ∧ e.2.1 = addrnd)) with _ | e
    · simp only [hf]
      erw [simulateQ_spec_query]
      simp [KeyedHash.ITSROracles, itsrProblem, hmsgFamily]
    · simp only [hf]
      simp

theorem sim_run {α : Type}
    (oa : OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) α)
    (log : G2Log prims) :
    (simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims))
        ((simulateQ (implB (optRand := optRand) pkSeed root pk signR) oa).run log)).run
        (targetsOf pkSeed root log) =
      (fun z => (z, targetsOf pkSeed root z.2)) <$>
        (simulateQ (implG (optRand := optRand) pk signR) oa).run log := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [sim_step]
    simp only [bind_map_left, map_bind]
    exact bind_congr fun z => ih z.1 z.2

theorem logCovered_append (log : G2Log prims) (msg : List Byte) (a R : prims.Y)
    (h : LogCovered pkSeed root log)
    (hR : ∀ e0, log.find? (fun e => decide (e.1 = msg ∧ e.2.1 = a)) = some e0 → R = e0.2.2) :
    LogCovered pkSeed root (log ++ [(msg, a, R)]) := by
  intro e he
  rw [targetsOf_append, List.mem_append]
  rcases List.mem_append.1 he with he | he
  · exact Or.inl (h e he)
  · obtain rfl : e = (msg, a, R) := by simpa using he
    rcases hf : log.find? (fun e => decide (e.1 = msg ∧ e.2.1 = a)) with _ | e0
    · right; simp only [hf]; simp
    · left
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      have h3 := h e0 h2
      simp only [decide_eq_true_eq] at h1
      rw [hR e0 hf, ← h1.1]
      exact h3

theorem g_step_covered (t : ℕ ⊕ List Byte) (log : G2Log prims)
    (h : LogCovered pkSeed root log) :
    ∀ z ∈ support ((implG (optRand := optRand) pk signR t).run log),
      LogCovered pkSeed root z.2 := by
  intro z hz
  rcases t with n | msg
  · simp [implG] at hz
    obtain ⟨_, rfl⟩ := hz
    exact h
  · simp only [implG, g2SignOracle, QueryImpl.add_apply_inr] at hz
    simp at hz
    obtain ⟨a, _, R, hR, rfl⟩ := hz
    refine logCovered_append pkSeed root log msg a R h fun e0 he0 => ?_
    simp only [lazyRandomizer, he0] at hR
    simpa using hR

theorem g_run_covered {α : Type}
    (oa : OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) α)
    (log : G2Log prims) (h : LogCovered pkSeed root log) :
    ∀ z ∈ support ((simulateQ (implG (optRand := optRand) pk signR) oa).run log),
      LogCovered pkSeed root z.2 := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => intro z hz; simp at hz; subst hz; exact h
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨y, hy, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    exact ih y.1 y.2 (g_step_covered pkSeed root pk signR t log h y hy) z hz

end Sim

theorem support_joint_aux {α β γ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → ProbComp γ) (w : α × β × γ)
    (hw : w ∈ support (do
      let a ← mx
      let b ← my
      let z ← f a b
      return (a, b, z))) : w.2.2 ∈ support (f w.1 w.2.1) := by
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨a, -, b, -, z, hz, rfl⟩ := hw
  exact hz

theorem g2Joint_covered (A : Forger vp prims optRand pkSeedDist) :
    ∀ w ∈ support (g2Joint A),
      LogCovered w.1 (idealPk vp prims w.2.1 w.1).pkRoot w.2.2.2 := by
  intro w hw
  have hz := support_joint_aux pkSeedDist (sampleTable vp prims)
    (fun a b => g2Run A b (idealPk vp prims b a)) w hw
  have h0 : LogCovered w.1 (idealPk vp prims w.2.1 w.1).pkRoot ([] : G2Log prims) :=
    fun e he => nomatch he
  exact g_run_covered (optRand := optRand) w.1 (idealPk vp prims w.2.1 w.1).pkRoot
    (idealPk vp prims w.2.1 w.1)
    (fun m R => idealSign vp prims w.2.1 m (idealPk vp prims w.2.1 w.1) R)
    (A.main (idealPk vp prims w.2.1 w.1)) [] h0 w.2.2 hz

theorem run_aux {α β γ δ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → OracleComp (itsrSpec prims) γ) (g : α → β → γ → δ) :
    (simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims)) (do
      let a ← (liftM mx : OracleComp (itsrSpec prims) α)
      let b ← (liftM my : OracleComp (itsrSpec prims) β)
      let c ← f a b
      return g a b c)).run [] = (do
      let a ← mx
      let b ← my
      let c ← (simulateQ (KeyedHash.ITSROracles (itsrProblem vp prims)) (f a b)).run []
      return (g a b c.1, c.2)) := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_itsr_liftM_run, bind_map_left,
    simulateQ_pure, StateT.run_pure]

theorem bItsr_run (A : Forger vp prims optRand pkSeedDist) :
    (bItsr A).run = (do
      let pkSeed ← pkSeedDist
      let tbl ← sampleTable vp prims
      let z ← g2Run A tbl (idealPk vp prims tbl pkSeed)
      return ((z.1.2.randomness, (pkSeed, (idealPk vp prims tbl pkSeed).pkRoot, z.1.1)),
        targetsOf pkSeed (idealPk vp prims tbl pkSeed).pkRoot z.2)) := by
  refine (run_aux pkSeedDist (sampleTable vp prims)
    (fun pkSeed tbl => runForgerLog A (idealPk vp prims tbl pkSeed)
      (itsrRandomizer pkSeed (idealPk vp prims tbl pkSeed).pkRoot)
      (fun m R => pure (idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R)))
    (fun pkSeed tbl c => (c.1.2.randomness,
      (pkSeed, (idealPk vp prims tbl pkSeed).pkRoot, c.1.1)))).trans ?_
  refine bind_congr fun pkSeed => bind_congr fun tbl => ?_
  have h := sim_run (optRand := optRand) pkSeed (idealPk vp prims tbl pkSeed).pkRoot
    (idealPk vp prims tbl pkSeed)
    (fun m R => idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R)
    (A.main (idealPk vp prims tbl pkSeed)) []
  rw [targetsOf_nil] at h
  refine (congrArg (· >>= _) h).trans ?_
  simp only [bind_map_left]
  rfl

theorem classify_itsr (pk : PublicKeyCore prims.core) (signed : List (List Byte × prims.Y))
    (msg : List Byte) (sig ref : GeneralScheme.SignatureCore vp prims.core)
    (hc : classify pk signed msg sig ref = .itsr) :
    ∀ x ∈ forsIndices vp (digestParts pk sig.randomness msg), x ∈ openedLeaves pk signed := by
  unfold classify at hc
  dsimp only at hc
  split_ifs at hc with h1
  exact h1

/-- The deterministic core of Step 4: a fresh forgery of class `itsr` wins ITSR against the
targets of a covered transcript. -/
theorem wins_of_itsr (pk : PublicKeyCore prims.core) (log : G2Log prims) (msg : List Byte)
    (sig ref : GeneralScheme.SignatureCore vp prims.core)
    (hcov : LogCovered pk.pkSeed pk.pkRoot log) (hfresh : msg ∉ log.map (·.1))
    (hc : classify pk (G2Log.signed log) msg sig ref = .itsr) :
    (itsrProblem vp prims).Wins (targetsOf pk.pkSeed pk.pkRoot log)
      (sig.randomness, (pk.pkSeed, pk.pkRoot, msg)) := by
  refine ⟨fun hmem => ?_, fun i hi => ?_⟩
  · obtain ⟨e, he, heq⟩ := mem_targetsOf _ _ _ _ hmem
    have h1 : msg = e.1 := congrArg (fun x => x.2.2.2) heq
    exact hfresh (List.mem_map.2 ⟨e, he, h1.symm⟩)
  · have h := classify_itsr pk _ msg sig ref hc i hi
    unfold openedLeaves G2Log.signed at h
    rw [List.mem_flatMap] at h
    obtain ⟨e', he', hi'⟩ := h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact List.mem_flatMap.2 ⟨_, hcov e he, hi'⟩

/-- **Step 4.** -/
theorem stepITSR (A : Forger vp prims optRand pkSeedDist) : StepITSR A (bItsr A) := by
  unfold StepITSR
  have hR : KeyedHash.ITSRExperiment (bItsr A) = g2Joint A >>= fun w =>
      pure (decide ((itsrProblem vp prims).Wins
        (targetsOf w.1 (idealPk vp prims w.2.1 w.1).pkRoot w.2.2.2)
        (w.2.2.1.2.randomness, (w.1, (idealPk vp prims w.2.1 w.1).pkRoot, w.2.2.1.1)))) := by
    simp [KeyedHash.ITSRExperiment, bItsr_run, g2Joint]
  rw [KeyedHash.ITSRAdvantage_eq_evalDist_experiment, hR, g2Class_eq_joint]
  change prTrue _ ≤ prTrue _
  rw [prTrue_bind_pure, prTrue_bind_pure]
  refine prEvent_mono_of_support _ _ _ fun w hw h => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨hv, hc⟩ := h
  unfold g2Valid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact wins_of_itsr (idealPk vp prims w.2.1 w.1) w.2.2.2 w.2.2.1.1 w.2.2.1.2 _
    (g2Joint_covered A w hw) hv.1 hc

theorem itsrRandomizer_bound (pkSeed : prims.PkSeed) (root : prims.Y) (log : G2Log prims)
    (m : List Byte) (a : prims.Y) :
    IsQueryBoundP (itsrRandomizer pkSeed root log m a) (fun i => i.isRight = true) 1 := by
  unfold itsrRandomizer
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

theorem logSignOracle_bound (pkSeed : prims.PkSeed) (root : prims.Y)
    (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core)
    (msg : List Byte) (log : G2Log prims) :
    IsQueryBoundP ((logSignOracle optRand pk (itsrRandomizer pkSeed root)
      (fun m R => (pure (signR m R) : OracleComp (itsrSpec prims) _)) msg).run log)
      (fun i => i.isRight = true) 1 := by
  simp only [logSignOracle]
  simp
  exact isQueryBoundP_bind (n := 0) (m := 1)
    (isQueryBoundP_liftM_isRight (hs := KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y)
      (optRand pk))
    (fun a _ => (isQueryBoundP_map_iff _ _ _).2 (itsrRandomizer_bound pkSeed root log msg a))

theorem bound_aux {α β γ δ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → OracleComp (itsrSpec prims) γ) (g : α → β → γ → δ) (n : ℕ)
    (h : ∀ a b, IsQueryBoundP (f a b) (fun i => i.isRight = true) n) :
    IsQueryBoundP (do
      let a ← (liftM mx : OracleComp (itsrSpec prims) α)
      let b ← (liftM my : OracleComp (itsrSpec prims) β)
      let c ← f a b
      return g a b c) (fun i => i.isRight = true) n := by
  have h' := isQueryBoundP_bind
    (isQueryBoundP_liftM_isRight (hs := KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y) mx)
    (fun a _ => isQueryBoundP_bind
      (isQueryBoundP_liftM_isRight (hs := KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y) my)
      (fun b _ => isQueryBoundP_bind (h a b)
        (fun c _ => isQueryBoundP_pure (fun (i : ℕ ⊕ ItsrIn prims) => i.isRight = true)
          (g a b c) 0)))
  exact h'.mono (by omega)

/-- Resource lemma: at most one ITSR target per signing query. -/
theorem bItsr_queryBound (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bItsr A).main (fun i => i.isRight = true) qs := by
  have key : ∀ (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims),
      IsQueryBoundP (runForgerLog A (idealPk vp prims tbl pkSeed)
        (itsrRandomizer pkSeed (idealPk vp prims tbl pkSeed).pkRoot)
        (fun m R => pure (idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R)))
        (fun i => i.isRight = true) qs := by
    intro pkSeed tbl
    refine IsQueryBoundP.simulateQ_run_add_inr_of_step (fun t => by simp) (hA _)
      (fun t s => ?_) (fun t _ s => logSignOracle_bound _ _ _ _ t s)
      (fun t ht => absurd rfl ht) []
    simp
    exact isQueryBoundP_liftM_isRight (hs := KeyedHash.ITSRTargetSpec (ItsrIn prims) prims.Y)
      (liftM (unifSpec.query t) : ProbComp _)
  exact bound_aux pkSeedDist (sampleTable vp prims)
    (fun pkSeed tbl => runForgerLog A (idealPk vp prims tbl pkSeed)
      (itsrRandomizer pkSeed (idealPk vp prims tbl pkSeed).pkRoot)
      (fun m R => pure (idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R)))
    (fun pkSeed tbl c => (c.1.2.randomness,
      (pkSeed, (idealPk vp prims tbl pkSeed).pkRoot, c.1.1))) qs key

end Reduction

#print axioms Reduction.stepSplit
#print axioms Reduction.stepITSR
#print axioms Reduction.bItsr_queryBound
