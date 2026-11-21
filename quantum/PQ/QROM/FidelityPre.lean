import PQ.QROM.FidelityLazy
import PQ.QROM.ExactGenPre
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE

/-!
# Fidelity of the exact SM-DT-PRE game to VCVio's `SM_DT_PRE_Experiment`

`genPreSubExp` (`PQ/QROM/ExactGenPre.lean`: planted inputs `xs : Tw → Mp` pre-sampled, embedding
`emb : Mp ↪ Msg`, preimage returned in `Mp`), restricted to classical adversaries with one
uniform coin, is VCVio's `SM_DT_PRE_Advantage` at a uniformly random tweakable hash.

* `fidPreProblem cap emb Th : SM_DT_PRE_Problem Unit Sd Tw Msg Mp Y`: hash `Th (P, (t, m))`,
  seed uniform, `emb`, cap `cap`, collection: the same function.
* `FidPreAdv Ω Sd Tw Msg Mp Y`, `FidPreAdv.honest cap emb A Th`.
* `fidPreEag`: VCVio's two oracles with the challenge oracle's fresh draw `x ← $ᵗ Mp` replaced
  by the entry `xs t` of a table (on VCVio's state).
* `fid_pre_presample`: **pre-sampling**: for every continuation, VCVio's first phase (fresh
  draws) followed by the continuation has the probability of the average over uniform tables
  `xs` of the deterministic table-run followed by the continuation.  (A tweak is accepted at
  most once, so each entry is read at most once: `fidLazy_eq_eager`.)
* `fid_pre_eag_run`: the table-run is the classical run against the challenger `genPreCh` of
  the exact game, under the state correspondence `fidPreSt xs`.
* `fid_pre_genPreSubExp_eq`:
  `genPreSubExp (embedding) = avg_Th SM_DT_PRE_Advantage (A.honest cap emb Th)`.
* `fid_pre_classical_le`: `gen_pre_sub_exact_le` as a bound on VCVio's advantage.
-/

open OracleComp OracleSpec TweakableHash ENNReal Quantum Matrix

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Sd Tw Msg Mp Ω : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Mp] [DecidableEq Mp] [Nonempty Mp]
  [SampleableType Sd] [SampleableType Mp] [Fintype Ω] [Nonempty Ω] [SampleableType Ω]

/-- VCVio's SM-DT-PRE problem for the hash `Th`. -/
def fidPreProblem (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) :
    SM_DT_PRE_Problem Unit Sd Tw Msg Mp Y where
  th := ⟨$ᵗ Sd, fun P t m ↦ Th (P, (t, m))⟩
  emb := emb
  emb_injective := emb.injective
  thColl := ⟨fun _ ↦ Msg, fun _ P t m ↦ Th (P, (t, m))⟩
  numTargets := cap

/-- The request oracles of SM-DT-PRE: challenge oracle, collection oracle. -/
abbrev fidPreReqSpec (Tw Msg Y : Type) := SM_DT_PRE_challengeSpec Tw Y + fidCollSpec Tw Msg Y

/-- Requests of the exact game for the queries of the two oracles. -/
def fidPreCodec (Tw Msg Y : Type) :
    FidCodec (fidPreReqSpec Tw Msg Y) (Tw ⊕ (Tw × Msg)) (Option Y) where
  enc r := match r with
    | .inl t => .inl t
    | .inr q => .inr q.2
  dec r y := match r with
    | .inl _ => y
    | .inr _ => y
  dflt r := match r with
    | .inl _ => (none : Option Y)
    | .inr _ => (none : Option Y)

/-- A classical SM-DT-PRE adversary with a uniform coin drawn at the start. -/
structure FidPreAdv (Ω Sd Tw Msg Mp Y : Type) where
  /-- Private state carried from `choose` to `invert`. -/
  State : Type
  /-- The first phase, for the coin `ω`. -/
  choose : Ω → OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State
  /-- The second phase. -/
  invert : State → Sd → OracleComp (Dom Sd Tw Msg →ₒ Y) (ℕ × Mp)

/-- Answer hash queries with `Th`; pass challenge and collection queries on. -/
def fidPreInst (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) :
    QueryImpl ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) (OracleComp (unifSpec +
      (SM_DT_PRE_challengeSpec Tw Y + collectionSpec (fidPreProblem cap emb Th).thColl))) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => liftM (OracleSpec.query (spec := unifSpec +
      (SM_DT_PRE_challengeSpec Tw Y + collectionSpec (fidPreProblem cap emb Th).thColl)) (.inr r))

/-- VCVio's adversary at the hash `Th`. -/
noncomputable def FidPreAdv.honest (cap : ℕ) (emb : Mp ↪ Msg) (A : FidPreAdv Ω Sd Tw Msg Mp Y)
    (Th : Dom Sd Tw Msg → Y) : SM_DT_PRE_Adversary (fidPreProblem cap emb Th) where
  State := A.State
  choose := do
    let ω ← (liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (unifSpec +
      (SM_DT_PRE_challengeSpec Tw Y + collectionSpec (fidPreProblem cap emb Th).thColl)) Ω)
    simulateQ (fidPreInst cap emb Th) (A.choose ω)
  invert st P := simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.invert st P)

/-- VCVio's oracles with hash queries answered by `Th`, as one implementation. -/
noncomputable def fidPreImpl (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd) :
    QueryImpl ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y)
      (StateT (SM_DT_PRE_State Tw Mp) ProbComp) :=
  fun t ↦ match t with
    | .inl q => pure (Th q)
    | .inr r => SM_DT_PRE_oracles (fidPreProblem cap emb Th) P (.inr r)

theorem fid_pre_compose (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    {State : Type} (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State) :
    simulateQ (SM_DT_PRE_oracles (fidPreProblem cap emb Th) P)
        (simulateQ (fidPreInst cap emb Th) oa) =
      simulateQ (fidPreImpl cap emb Th P) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind (fidPreInst cap emb Th), simulateQ_spec_query,
      simulateQ_bind (fidPreImpl cap emb Th P), simulateQ_spec_query, simulateQ_bind]
    rcases t with q | r
    · simp only [fidPreInst, fidPreImpl]
      rw [simulateQ_pure, pure_bind, pure_bind]
      exact ih (Th q)
    · simp only [fidPreInst, fidPreImpl]
      refine Eq.trans (congrArg (· >>= _) (simulateQ_spec_query
        (SM_DT_PRE_oracles (fidPreProblem cap emb Th) P) (.inr r))) ?_
      exact bind_congr fun u ↦ ih u

/-- VCVio's two oracles with the fresh draw of the challenge oracle replaced by the entry of
the table `xs`, as deterministic steps on VCVio's state. -/
def fidPreEag (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd) (xs : Tw → Mp) :
    (t : ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y).Domain) → SM_DT_PRE_State Tw Mp →
      ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y).Range t × SM_DT_PRE_State Tw Mp
  | .inl q, s => (Th q, s)
  | .inr (.inl t), s =>
    if cap ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 t then ((none : Option Y), s)
    else (some (Th (P, (t, emb (xs t)))), (s.1 ++ [(t, xs t)], s.2))
  | .inr (.inr q), s =>
    if TweakReserved Prod.fst s.1 q.2.1 then ((none : Option Y), s)
    else (some (Th (P, (q.2.1, q.2.2))), (s.1, s.2 ++ [q.2.1]))

/-- **Pre-sampling of the planted inputs.** -/
theorem fid_pre_presample (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    {State : Type} (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State)
    (s : SM_DT_PRE_State Tw Mp) (cont : State × SM_DT_PRE_State Tw Mp → ProbComp Bool) :
    fidPr ((simulateQ (SM_DT_PRE_oracles (fidPreProblem cap emb Th) P)
        (simulateQ (fidPreInst cap emb Th) oa)).run s >>= cont) =
      avg fun xs : Tw → Mp ↦ fidPr (cont (fidEagRun (fidPreEag cap emb Th P xs) oa s)) := by
  rw [fid_pre_compose]
  refine fidLazy_eq_eager (dead := fun s i ↦ TweakReserved Prod.fst s.1 i) ?_ ?_ ?_ oa s cont
  · intro t s
    rcases t with q | t | q
    · exact Or.inl fun xs ↦ rfl
    · by_cases h : cap ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 t
      · left
        intro xs
        change (SM_DT_PRE_challengeOracle (fidPreProblem cap emb Th) P t).run s = _
        simp [fidPreEag, SM_DT_PRE_challengeOracle, fidPreProblem, h]
      · right
        refine ⟨t, fun x ↦ (some (Th (P, (t, emb x))), (s.1 ++ [(t, x)], s.2)), ?_, ?_, ?_⟩
        · change (SM_DT_PRE_challengeOracle (fidPreProblem cap emb Th) P t).run s = _
          simp [SM_DT_PRE_challengeOracle, fidPreProblem, h, map_eq_bind_pure_comp]
        · intro xs
          simp [fidPreEag, h]
        · intro x
          exact ⟨(t, x), by simp, rfl⟩
    · left
      intro xs
      change (collectionOracle (Q := Tw × Mp) Prod.fst (fidPreProblem cap emb Th).thColl P q).run
        s = _
      by_cases h : TweakReserved Prod.fst s.1 q.2.1
      · simp [fidPreEag, collectionOracle, fidPreProblem, h]
      · simp [fidPreEag, collectionOracle, fidPreProblem, h]
  · intro xs t s i hi
    rcases t with q | t | q
    · exact hi
    · simp only [fidPreEag]
      split_ifs
      · exact hi
      · obtain ⟨e, he, heq⟩ := hi
        exact ⟨e, List.mem_append_left _ he, heq⟩
    · simp only [fidPreEag]
      split_ifs
      · exact hi
      · exact hi
  · intro xs t s i x hi
    rcases t with q | t | q
    · rfl
    · by_cases hti : t = i
      · subst hti
        have h : cap ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 t := Or.inr fun hf ↦ hf.1 hi
        simp [fidPreEag, h]
      · simp [fidPreEag, Function.update_of_ne hti]
    · rfl

/-- VCVio's game state for the histories of the exact game and the table `xs`. -/
def fidPreSt (xs : Tw → Mp) (s : PreState Tw Msg) : SM_DT_PRE_State Tw Mp :=
  (s.chal.map fun t ↦ (t, xs t), s.coll.map Prod.fst)

theorem fid_pre_reserved_iff (xs : Tw → Mp) (s : PreState Tw Msg) (t : Tw) :
    TweakReserved Prod.fst (fidPreSt xs s).1 t ↔ t ∈ s.chal := by
  simp [TweakReserved, fidPreSt]

/-- The table-step of VCVio's challenge oracle is the challenger `genPreCh` of the exact game. -/
theorem fid_pre_step_chal (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (xs : Tw → Mp) (t : Tw) (s : PreState Tw Msg) :
    fidPreEag cap emb Th P xs (.inr (.inl t)) (fidPreSt xs s) =
      ((genPreCh cap emb xs (rowOf Th P) (.inl t) s).1,
        fidPreSt xs (genPreCh cap emb xs (rowOf Th P) (.inl t) s).2) := by
  have hc : (cap ≤ (fidPreSt xs s).1.length ∨
      ¬ TweakFresh Prod.fst (fidPreSt xs s).1 (fidPreSt xs s).2 t) ↔
      (cap ≤ s.chal.length ∨ t ∈ s.chal ∨ t ∈ s.coll.map Prod.fst) := by
    unfold TweakFresh
    rw [fid_pre_reserved_iff]
    simp only [fidPreSt, List.length_map]
    tauto
  simp only [fidPreEag, genPreCh, preChT]
  by_cases h : cap ≤ s.chal.length ∨ t ∈ s.chal ∨ t ∈ s.coll.map Prod.fst
  · rw [if_pos (hc.2 h), dif_pos h]
  · rw [if_neg (fun h' ↦ h (hc.1 h')), dif_neg h]
    simp [fidPreSt, rowOf]

/-- The table-step of VCVio's collection oracle is the challenger `genPreCh` of the exact
game. -/
theorem fid_pre_step_coll (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (xs : Tw → Mp) (q : (_ : Unit) × Tw × Msg) (s : PreState Tw Msg) :
    fidPreEag cap emb Th P xs (.inr (.inr q)) (fidPreSt xs s) =
      ((genPreCh cap emb xs (rowOf Th P) (.inr q.2) s).1,
        fidPreSt xs (genPreCh cap emb xs (rowOf Th P) (.inr q.2) s).2) := by
  simp only [fidPreEag, genPreCh, preChT]
  by_cases h : q.2.1 ∈ s.chal
  · rw [if_pos ((fid_pre_reserved_iff xs s _).2 h), dif_pos h]
  · rw [if_neg (fun h' ↦ h ((fid_pre_reserved_iff xs s _).1 h')), dif_neg h]
    simp [fidPreSt, rowOf]

/-- The table-run of VCVio's first phase is the classical run against the challenger
`genPreCh` of the exact game. -/
theorem fid_pre_eag_run (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (xs : Tw → Mp) {State : Type}
    (oa : OracleComp ((Dom Sd Tw Msg →ₒ Y) + fidPreReqSpec Tw Msg Y) State)
    (s : PreState Tw Msg) :
    fidEagRun (fidPreEag cap emb Th P xs) oa (fidPreSt xs s) =
      ((fidGRun (fidPreCodec Tw Msg Y) Th (genPreCh cap emb xs (rowOf Th P)) oa s).1,
        fidPreSt xs (fidGRun (fidPreCodec Tw Msg Y) Th (genPreCh cap emb xs (rowOf Th P)) oa
          s).2) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with q | t | q
    · exact ih (Th q) s
    · change fidEagRun _ (k (fidPreEag cap emb Th P xs (.inr (.inl t)) (fidPreSt xs s)).1)
        (fidPreEag cap emb Th P xs (.inr (.inl t)) (fidPreSt xs s)).2 = _
      rw [fid_pre_step_chal]
      exact ih _ _
    · change fidEagRun _ (k (fidPreEag cap emb Th P xs (.inr (.inr q)) (fidPreSt xs s)).1)
        (fidPreEag cap emb Th P xs (.inr (.inr q)) (fidPreSt xs s)).2 = _
      rw [fid_pre_step_coll]
      exact ih _ _

/-- Reversing the order of four uniform averages. -/
theorem avg_reverse4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ≥0∞) :
    (avg fun a ↦ avg fun b ↦ avg fun c ↦ avg fun d ↦ f a b c d) =
      avg fun d ↦ avg fun c ↦ avg fun b ↦ avg fun a ↦ f a b c d := by
  rw [avg_comm, avg_congr fun b ↦ avg_comm _,
    avg_congr fun b ↦ avg_congr fun c ↦ avg_comm _, avg_comm,
    avg_congr fun c ↦ avg_comm _, avg_comm]

/-- The rest of VCVio's experiment after the first phase. -/
noncomputable def fidPreCont (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y)
    (A : FidPreAdv Ω Sd Tw Msg Mp Y) (P : Sd) (z : A.State × SM_DT_PRE_State Tw Mp) :
    ProbComp Bool := do
  let (j, m) ← simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.invert z.1 P)
  match z.2.1[j]? with
  | none => return false
  | some (t, x) =>
      return decide ((fidPreProblem cap emb Th).th.eval P t ((fidPreProblem cap emb Th).emb m) =
        (fidPreProblem cap emb Th).th.eval P t ((fidPreProblem cap emb Th).emb x))

theorem fid_pre_run_lift {α : Type} (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y) (P : Sd)
    (oa : ProbComp α) (s : SM_DT_PRE_State Tw Mp) :
    (simulateQ (SM_DT_PRE_oracles (fidPreProblem cap emb Th) P)
      (liftM oa : OracleComp (unifSpec +
      (SM_DT_PRE_challengeSpec Tw Y + collectionSpec (fidPreProblem cap emb Th).thColl)) α)).run s =
      oa >>= fun a ↦ pure (a, s) := by
  unfold SM_DT_PRE_oracles
  rw [QueryImpl.simulateQ_add_liftM_left]
  simp

theorem fid_pre_experiment (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y)
    (A : FidPreAdv Ω Sd Tw Msg Mp Y) :
    SM_DT_PRE_Experiment (A.honest cap emb Th) =
      (do
        let P ← $ᵗ Sd
        let ω ← $ᵗ Ω
        (simulateQ (SM_DT_PRE_oracles (fidPreProblem cap emb Th) P)
          (simulateQ (fidPreInst cap emb Th) (A.choose ω))).run ([], []) >>=
            fidPreCont cap emb Th A P : ProbComp Bool) := by
  unfold SM_DT_PRE_Experiment
  refine bind_congr (m := ProbComp) fun P ↦ ?_
  simp only [FidPreAdv.honest]
  rw [simulateQ_bind, StateT.run_bind, fid_pre_run_lift]
  simp only [bind_assoc, pure_bind]
  rfl

open Classical in
/-- The rest of VCVio's experiment, on the state of a table-run, is the winning condition
`genPreSubWin` of the exact game. -/
theorem fid_pre_cont (cap : ℕ) (emb : Mp ↪ Msg) (Th : Dom Sd Tw Msg → Y)
    (A : FidPreAdv Ω Sd Tw Msg Mp Y) (P : Sd) (xs : Tw → Mp) (a : A.State)
    (s : PreState Tw Msg) :
    fidPr (fidPreCont cap emb Th A P (a, fidPreSt xs s)) =
      ind (genPreSubWin emb xs (rowOf Th P)
        (evalWithAnswerFn (QueryImpl.ofFn Th) (A.invert a P)) s) := by
  unfold fidPreCont
  rw [fid_simulateQ_pure, pure_bind]
  set r := evalWithAnswerFn (QueryImpl.ofFn Th) (A.invert a P)
  have hget : (fidPreSt xs s).1[r.1]? = (s.chal[r.1]?).map fun t ↦ (t, xs t) := by
    simp [fidPreSt]
  simp only [hget]
  unfold genPreSubWin
  rcases hg : s.chal[r.1]? with _ | t
  · rw [Option.map_none, fidPr_pure, ind_of_false (by simp), ind_of_false (by simp)]
  · rw [Option.map_some, fidPr_pure]
    by_cases hc : Th (P, (t, emb r.2)) = Th (P, (t, emb (xs t)))
    · exact (ind_of_true (decide_eq_true_iff.2 hc)).trans
        (ind_of_true ⟨t, rfl, by simpa [rowOf] using hc⟩).symm
    · refine (ind_of_false (fun h' ↦ hc (decide_eq_true_iff.1 h'))).trans (ind_of_false ?_).symm
      rintro ⟨t', ht', heq⟩
      cases Option.some.inj ht'
      exact hc (by simpa [rowOf] using heq)

/-- **Fidelity of the exact SM-DT-PRE game.** -/
theorem fid_pre_genPreSubExp_eq (cap : ℕ) (emb : Mp ↪ Msg) (A : FidPreAdv Ω Sd Tw Msg Mp Y)
    (n : ℕ) (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n) :
    genPreSubExp .instruments (A := QReg.of Unit) (SubState.basis ()) cap n emb
        (fidGCoinEmb (fidPreCodec Tw Msg Y) A.choose n) (fidGPh2 A.invert) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_PRE_Advantage (A.honest cap emb Th) := by
  unfold genPreSubExp SM_DT_PRE_Advantage
  rw [avg_congr fun xs ↦ fidGCoin_twoPhaseExp (fidPreCodec Tw Msg Y) (genPreCh cap emb xs) preInit
    (genPreSubWin emb xs) n A.choose (fidGPh2 A.invert)]
  unfold twoPhaseExp
  rw [avg_reverse4]
  refine avg_congr fun Th ↦ ?_
  rw [fid_pre_experiment]
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun P ↦ ?_
  refine Eq.trans ?_ (fidPr_uniform_bind _).symm
  refine avg_congr fun ω ↦ ?_
  rw [fid_pre_presample]
  refine avg_congr fun xs ↦ ?_
  rw [fidG_realProb _ _ _ _ _ _ _ (hb ω)]
  have h := fid_pre_eag_run cap emb Th P xs (A.choose ω) preInit
  rw [show (([], []) : SM_DT_PRE_State Tw Mp) = fidPreSt xs preInit from rfl, h, fid_pre_cont]

/-- **`gen_pre_sub_exact_le` as a bound on VCVio's SM-DT-PRE advantage**, averaged over the
uniformly random tweakable hash. -/
theorem fid_pre_classical_le [Inhabited Tw] (cap : ℕ) (emb : Mp ↪ Msg)
    (A : FidPreAdv Ω Sd Tw Msg Mp Y) (n q₁ q₂ : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n)
    (h1 : ∀ ω, IsQueryBoundP (A.choose ω) fidIsHash q₁)
    (h2 : ∀ st P, IsTotalQueryBound (A.invert st P) q₂) :
    (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_PRE_Advantage (A.honest cap emb Th)) ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [← fid_pre_genPreSubExp_eq cap emb A n hb]
  exact gen_pre_sub_exact_le (fidGCoin_emb_isQueryBound _ A.choose n q₁ h1)
    (fidG_ph2_isQueryBound A.invert q₂ h2)

end PQ.QROM

#print axioms PQ.QROM.fid_pre_presample
#print axioms PQ.QROM.fid_pre_eag_run
#print axioms PQ.QROM.fid_pre_genPreSubExp_eq
#print axioms PQ.QROM.fid_pre_classical_le
