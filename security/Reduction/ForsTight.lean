import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR

/-!
# SM-DT-OpenPRE from SM-DT-DSPR and SM-DT-TCR (generic, unconditional)

For an **arbitrary** SM-DT-OpenPRE adversary `adv` against an arbitrary problem with uniform
hidden inputs (`prob.HasUniformInputs`):

`Adv^{OpenPRE}(adv) ≤ Adv^{DSPR}(toDSPR adv) + 3 · Adv^{TCR}(toTCR adv)`

(`ForsTight.openPRE_le_dspr_add_three_tcr`), where
* `toDSPR adv`, `toTCR adv` are VCVio's explicit black-box reductions
  (`TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.toDSPR/toTCR`): each runs `adv.pick` once,
  samples one input per retained tweak, submits these `(tweak, input)` pairs as its targets,
  runs `adv.find` once answering openings from the sampled inputs, and post-processes the output
  in constant time;
* the DSPR advantage is `Pr[DSPR] − Pr[SPprob]` (truncated), exactly the paper's
  `max 0 (DSPR − SPprob)` (Hülsing–Kudinov, ePrint 2022/346; EasyCrypt
  `OpenPRE_From_TCR_DSPR_THF.eca`), and the coefficient of TCR is the paper's `3`.

This discharges, by a direct proof, the implication that VCVio leaves conditional on
`CountingInterface`.  Nothing here depends on how `adv` is built.

Proof.  All four experiments (OpenPRE, TCR, DSPR, SPprob) are the same random experiment `raw`
followed by four different Boolean predicates (`experiment_eq`, `tcr_experiment_eq`,
`dspr_experiment_eq`, `sp_experiment_eq`).  Pointwise,
`W + S ≤ D + T + 2·E₁`, where `E₁` is "the adversary returned exactly the hidden input of an
unopened target that has a second preimage".  `Pr[E₁] ≤ Pr[E₂] ≤ Pr[T]`, where `E₂` is "it
returned a different preimage": for each index `i`, replacing the hidden input `xᵢ` by `σ(xᵢ)`,
for a permutation `σ` of the message space that preserves the fibres of the hash and moves every
point of a fibre of size `≥ 2`, preserves the distribution of the inputs and — as long as target
`i` is not opened — the distribution of the adversary's run (`find_run_congr`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal MeasureTheory

namespace Reduction.ForsTight

open TweakableHash
open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity

variable {ι PkSeed Tweak M Y : Type}

/-! ## Sampling targets up front -/

/-- One hidden input per tweak, sampled independently from `gen`. -/
def sampleT (gen : ProbComp M) : List Tweak → ProbComp (List (Tweak × M))
  | [] => pure []
  | t :: ts => do
      let x ← gen
      let r ← sampleT gen ts
      pure ((t, x) :: r)

/-- The images of a list of targets. -/
def images (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (tg : List (Tweak × M)) : List Y :=
  tg.map fun q => th.eval pk q.1 q.2

/-- Record a list of targets in the monitor. -/
def recAll [DecidableEq Tweak] (n : ℕ) (st : SourceFinalValidity.State (Tweak × M) Tweak)
    (tg : List (Tweak × M)) : SourceFinalValidity.State (Tweak × M) Tweak :=
  tg.foldl (fun s q => s.recordTarget n Prod.fst q) st

section Record

variable [DecidableEq Tweak]

theorem recAll_cons (n : ℕ) (st : SourceFinalValidity.State (Tweak × M) Tweak) (q : Tweak × M)
    (tg : List (Tweak × M)) :
    recAll n st (q :: tg) = recAll n (st.recordTarget n Prod.fst q) tg := rfl

theorem recAll_challenges (n : ℕ) (st : SourceFinalValidity.State (Tweak × M) Tweak)
    (tg : List (Tweak × M)) : (recAll n st tg).challenges = st.challenges ++ tg := by
  induction tg generalizing st with
  | nil => simp [recAll]
  | cons q tg ih => rw [recAll_cons, ih]; simp [SourceFinalValidity.State.recordTarget]

/-- The validity bit after recording depends only on the tweaks. -/
theorem recAll_valid_congr (n : ℕ) (st st' : SourceFinalValidity.State (Tweak × M) Tweak)
    (tg tg' : List (Tweak × M)) (hv : st.valid = st'.valid)
    (hc : st.challenges.map Prod.fst = st'.challenges.map Prod.fst)
    (hcol : st.collectionTweaks = st'.collectionTweaks)
    (ht : tg.map Prod.fst = tg'.map Prod.fst) :
    (recAll n st tg).valid = (recAll n st' tg').valid := by
  induction tg generalizing st st' tg' with
  | nil =>
    cases tg' with
    | nil => simpa [recAll] using hv
    | cons _ _ => simp at ht
  | cons q tg ih =>
    cases tg' with
    | nil => simp at ht
    | cons q' tg' =>
      simp only [List.map_cons, List.cons.injEq] at ht
      rw [recAll_cons, recAll_cons]
      have hlen : st.challenges.length = st'.challenges.length := by
        simpa using congrArg List.length hc
      refine ih _ _ _ ?_ ?_ hcol ht.2
      · have hres : TweakReserved Prod.fst st.challenges q'.1 ↔
            TweakReserved Prod.fst st'.challenges q'.1 := by
          have h1 : ∀ (l : List (Tweak × M)) (t : Tweak),
              TweakReserved Prod.fst l t ↔ t ∈ l.map Prod.fst := by
            intro l t; simp [TweakReserved]
          rw [h1, h1, hc]
        rw [Bool.eq_iff_iff]
        simp [SourceFinalValidity.State.recordTarget, TweakFresh, hv, hlen, hcol, ht.1, hres]
        intro _ _
        exact decide_eq_true_iff.symm
      · simp [SourceFinalValidity.State.recordTarget, hc, ht.1]

end Record

/-! ## The game's target sampling, in normal form -/

theorem initializeTargets_run [DecidableEq Tweak] (prob : Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) (ts : List Tweak) (st : State Tweak M) :
    (initializeTargets prob pk ts).run st =
      (fun tg => (images prob.th pk tg, recAll prob.numTargets st tg)) <$>
        sampleT prob.inputGen ts := by
  induction ts generalizing st with
  | nil => simp [initializeTargets, sampleT, images, recAll]
  | cons t ts ih =>
    simp only [initializeTargets, sampleT, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure, ih,
      bind_map_left, monadLift_self]
    rfl

/-! ## The common experiment -/

section Core

variable [DecidableEq Tweak] [Inhabited M]

/-- Outcome of the common experiment: seed, monitor after the commitment phase, sampled targets,
and the result `((j, m), opened)` of the inversion phase. -/
abbrev Raw (PkSeed Tweak M : Type) : Type :=
  PkSeed × State Tweak M × List (Tweak × M) × ((ℕ × M) × List ℕ)

/-- The experiment shared by the OpenPRE game and by the TCR, DSPR and SPprob games of the two
reductions: seed, commitment phase, target sampling, inversion phase. -/
def raw {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    ProbComp (Raw PkSeed Tweak M) := do
  let pk ← prob.th.seedGen
  let w ← (simulateQ (pickOracles prob pk) adv.pick).run .initial
  let tg ← sampleT prob.inputGen (w.1.2.take prob.numTargets)
  let z ← (simulateQ (findOracles tg) (adv.find w.1.1 pk (images prob.th pk tg))).run []
  pure (pk, w.2, tg, z)

/-- A winning predicate: the selected index names a sampled target, the monitor is valid, and the
condition `c pk t x j m opened` holds for that target `(t, x)`. -/
def pred (n : ℕ) (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool) (r : Raw PkSeed Tweak M) :
    Bool :=
  match r.2.2.1[r.2.2.2.1.1]? with
  | none => false
  | some (t, x) => (recAll n r.2.1 r.2.2.1).valid && c r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2

/-- The commitment phase issues no target: the challenge history stays empty. -/
theorem pick_challenges {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) (pk : PkSeed) :
    ∀ w ∈ support ((simulateQ (pickOracles prob pk) adv.pick).run .initial),
      w.2.challenges = [] :=
  OracleComp.simulateQ_run_preservesInv (pickOracles prob pk) (fun st => st.challenges = [])
    ((SourceFinalValidity.preservesInv_privateRandomness _).add (fun q st hst z hz => by
      rw [SourceFinalValidity.collectionOracle_run, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hst)) adv.pick .initial rfl

/-- OpenPRE winning condition. -/
def cW [DecidableEq Y] (th : TweakableHash PkSeed Tweak M Y) :
    PkSeed → Tweak → M → ℕ → M → List ℕ → Bool :=
  fun pk t x j m op => decide (j ∉ op) && decide (th.eval pk t m = th.eval pk t x)

/-- TCR winning condition. -/
def cT [DecidableEq M] [DecidableEq Y] (th : TweakableHash PkSeed Tweak M Y) :
    PkSeed → Tweak → M → ℕ → M → List ℕ → Bool :=
  fun pk t x _ m _ => decide (m ≠ x ∧ th.eval pk t m = th.eval pk t x)

/-- DSPR winning condition for the guess `x ≠ m ∨ j ∈ opened`. -/
def cD [Fintype M] [DecidableEq M] [DecidableEq Y] (th : TweakableHash PkSeed Tweak M Y) :
    PkSeed → Tweak → M → ℕ → M → List ℕ → Bool :=
  fun pk t x j m op =>
    decide (SecondPreimageExists th pk t x ↔ decide (x ≠ m ∨ j ∈ op) = true)

/-- SPprob condition. -/
def cS [Fintype M] [DecidableEq M] [DecidableEq Y] (th : TweakableHash PkSeed Tweak M Y) :
    PkSeed → Tweak → M → ℕ → M → List ℕ → Bool :=
  fun pk t x _ _ _ => decide (SecondPreimageExists th pk t x)

theorem experiment_eq [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    experiment adv = pred prob.numTargets (cW prob.th) <$> raw adv := by
  unfold experiment raw
  simp only [map_bind, map_pure]
  refine bind_congr fun pk => ?_
  refine bind_congr_of_forall_mem_support _ fun w hw => ?_
  have h0 := pick_challenges adv pk w hw
  obtain ⟨⟨s, tw⟩, st⟩ := w
  simp only [initializeTargets_run, bind_map_left]
  refine bind_congr fun tg => ?_
  have hc : (recAll prob.numTargets st tg).challenges = tg := by
    rw [recAll_challenges, h0]; rfl
  simp only [hc]
  refine bind_congr fun z => ?_
  obtain ⟨⟨j, m⟩, op⟩ := z
  simp only [pred, cW]
  cases tg[j]? with
  | none => rfl
  | some q => simp [Bool.and_assoc]

end Core

/-! ## The two reductions, in normal form -/

section Reductions

variable [DecidableEq Tweak] [Inhabited M]

/-- The challenge oracle of the TCR and DSPR games attacked by the reductions. -/
def redChallenge (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y)
      (StateT (State Tweak M) ProbComp) :=
  fun tm => do
    let st ← get
    set (st.recordTarget prob.numTargets Prod.fst tm)
    return prob.th.eval pk tm.1 tm.2

/-- The oracles of the TCR and DSPR games attacked by the reductions, written over the OpenPRE
problem (both games have literally these oracles: `redOracles_eq_tcr`, `redOracles_eq_dspr`). -/
def redOracles (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)) (StateT (State Tweak M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State Tweak M) ProbComp) +
    (redChallenge prob pk +
      SourceFinalValidity.collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk)

theorem redOracles_eq_tcr (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    SM_DT_TCR_SourceFinalValidity.oracles prob.toTCR pk = redOracles prob pk := rfl

theorem redOracles_eq_dspr (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    SM_DT_DSPR_SourceFinalValidity.oracles prob.toDSPR pk = redOracles prob pk := rfl

/-- Routing the commitment phase through the assumption game's oracles is the OpenPRE game's own
commitment phase. -/
theorem simulateQ_liftPick (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) {α : Type}
    (oa : OracleComp (unifSpec + SourceFinalValidity.collectionSpec prob.thColl) α) :
    simulateQ (redOracles prob pk) (simulateQ (liftPick prob) oa) =
      simulateQ (pickOracles prob pk) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with q | q
  · change simulateQ _ (liftM (query _)) = _
    erw [simulateQ_spec_query]; rfl
  · change simulateQ _ (liftM (query _)) = _
    erw [simulateQ_spec_query]; rfl

theorem red_liftM_run (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed) {α : Type}
    (oa : ProbComp α) (st : State Tweak M) :
    (simulateQ (redOracles prob pk)
      (liftM oa : OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
        SourceFinalValidity.collectionSpec prob.thColl)) α)).run st =
      (fun a => (a, st)) <$> oa := by
  have h : simulateQ (redOracles prob pk)
      (liftM oa : OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
        SourceFinalValidity.collectionSpec prob.thColl)) α) = liftM oa := by
    simp [redOracles, QueryImpl.simulateQ_add_liftM_left]
  rw [h]
  simp

/-- The reductions' target setup: one challenge query per retained tweak, at a freshly sampled
input.  The monitor ends in exactly the state of the OpenPRE game. -/
theorem reductionInitialize_run (prob : Problem ι PkSeed Tweak M Y) (pk : PkSeed)
    (ts : List Tweak) (st : State Tweak M) :
    (simulateQ (redOracles prob pk) (reductionInitialize prob ts)).run st =
      (fun tg => ((tg, images prob.th pk tg), recAll prob.numTargets st tg)) <$>
        sampleT prob.inputGen ts := by
  induction ts generalizing st with
  | nil => simp [reductionInitialize, sampleT, images, recAll]
  | cons t ts ih =>
    simp only [reductionInitialize, sampleT, simulateQ_bind, StateT.run_bind, red_liftM_run,
      bind_map_left, map_bind]
    refine bind_congr fun x => ?_
    rw [simulateQ_spec_query]
    have hq : redOracles prob pk (.inr (.inl (t, x))) = redChallenge prob pk (t, x) := rfl
    rw [hq]
    simp only [redChallenge, StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, ih,
      bind_map_left, StateT.run_pure, map_pure]
    rfl

/-- The selection phase shared by `toTCR adv` and `toDSPR adv` (`toTCR_choose`, `toDSPR_choose`). -/
noncomputable def redChoose {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)) (adv.State × List (Tweak × M) × List Y) :=
  simulateQ (liftPick prob) adv.pick >>= fun w =>
    reductionInitialize prob (w.2.take prob.numTargets) >>= fun r => pure (w.1, r.1, r.2)

theorem toTCR_choose {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    (toTCR adv).choose = redChoose adv := rfl

theorem toDSPR_choose [DecidableEq M] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : (toDSPR adv).choose = redChoose adv := rfl

/-- **Resource lemma for both reductions.**  The selection phase of `toTCR adv` (and of
`toDSPR adv`, which has the same `choose`) run inside its game: it runs `adv.pick` once
(forwarding its coins and collection queries unchanged), samples one input per retained tweak
and issues exactly these `(tweak, input)` pairs as challenge queries — at most `prob.numTargets`
of them, at the tweaks `adv` committed to — and ends with the monitor of the OpenPRE game. -/
theorem red_choose_run {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) (pk : PkSeed)
    (st : State Tweak M) :
    (simulateQ (redOracles prob pk) (redChoose adv)).run st =
      (simulateQ (pickOracles prob pk) adv.pick).run st >>= fun w =>
        sampleT prob.inputGen (w.1.2.take prob.numTargets) >>= fun tg =>
          pure ((w.1.1, tg, images prob.th pk tg), recAll prob.numTargets w.2 tg) := by
  simp only [redChoose, simulateQ_bind, StateT.run_bind, simulateQ_liftPick,
    reductionInitialize_run, simulateQ_pure, StateT.run_pure, bind_map_left]

/-- The sampled targets carry exactly the given tweaks. -/
theorem sampleT_fst (gen : ProbComp M) (ts : List Tweak) :
    ∀ tg ∈ support (sampleT gen ts), tg.map Prod.fst = ts := by
  induction ts with
  | nil => intro tg h; simp only [sampleT, support_pure, Set.mem_singleton_iff] at h; simp [h]
  | cons t ts ih =>
    intro tg h
    simp only [sampleT, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨x, -, r, hr, rfl⟩ := h
    simp [ih r hr]

/-- **Target count of both reductions.**  In every run of the selection phase of `toTCR adv` /
`toDSPR adv`, the challenge queries issued are exactly one per tweak of the retained prefix of
`adv`'s commitment (in order), hence at most `prob.numTargets`; the private state handed to the
second phase is `adv`'s own state plus these targets and their images. -/
theorem red_choose_targets {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob)
    (pk : PkSeed) :
    ∀ z ∈ support ((simulateQ (redOracles prob pk) (redChoose adv)).run .initial),
      ∃ w ∈ support ((simulateQ (pickOracles prob pk) adv.pick).run .initial),
        z.1.1 = w.1.1 ∧ z.2.challenges = z.1.2.1 ∧
          z.2.challenges.map Prod.fst = w.1.2.take prob.numTargets ∧
          z.2.challenges.length ≤ prob.numTargets := by
  intro z hz
  rw [red_choose_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w, hw, tg, htg, rfl⟩ := hz
  have hc : (recAll prob.numTargets w.2 tg).challenges = tg := by
    rw [recAll_challenges, pick_challenges adv pk w hw]; rfl
  have hfst := sampleT_fst _ _ tg htg
  refine ⟨w, hw, rfl, hc, by rw [hc, hfst], ?_⟩
  rw [hc, ← List.length_map (f := Prod.fst), hfst, List.length_take]
  exact Nat.min_le_left _ _

theorem tcr_experiment_eq [DecidableEq M] [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) :
    SM_DT_TCR_SourceFinalValidity.experiment (toTCR adv) =
      pred prob.numTargets (cT prob.th) <$> raw adv := by
  have h1 : SM_DT_TCR_SourceFinalValidity.experiment (toTCR adv) = (do
      let pk ← prob.th.seedGen
      let x ← (simulateQ (redOracles prob pk) (redChoose adv)).run .initial
      let y ← (simulateQ (findOracles x.1.2.1) (adv.find x.1.1 pk x.1.2.2)).run [] >>=
        fun z => pure z.1
      match x.2.challenges[y.1]? with
      | none => pure false
      | some (t, mj) => pure (x.2.valid &&
          decide (y.2 ≠ mj ∧ prob.th.eval pk t y.2 = prob.th.eval pk t mj))) := rfl
  rw [h1]
  unfold raw
  simp only [map_bind, map_pure, red_choose_run, bind_assoc, pure_bind]
  refine bind_congr fun pk => ?_
  refine bind_congr_of_forall_mem_support _ fun w hw => ?_
  have h0 := pick_challenges adv pk w hw
  refine bind_congr fun tg => ?_
  have hc : (recAll prob.numTargets w.2 tg).challenges = tg := by
    rw [recAll_challenges, h0]; rfl
  simp only [hc]
  refine bind_congr fun z => ?_
  obtain ⟨⟨j, m⟩, op⟩ := z
  simp only [pred, cT]
  cases tg[j]? with
  | none => rfl
  | some q => rfl

/-- The opening answer for index `j` is the hidden input of target `j`. -/
theorem sampled_eq (tg : List (Tweak × M)) (j : ℕ) (t : Tweak) (x : M)
    (h : tg[j]? = some (t, x)) : (tg[j]?.map Prod.snd).getD default = x := by
  simp [h]

theorem dspr_experiment_eq [Fintype M] [DecidableEq M] [DecidableEq Y]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.experiment (toDSPR adv) =
      pred prob.numTargets (cD prob.th) <$> raw adv := by
  have h1 : SM_DT_DSPR_SourceFinalValidity.experiment (toDSPR adv) = (do
      let pk ← prob.th.seedGen
      let x ← (simulateQ (redOracles prob pk) (redChoose adv)).run .initial
      let y ← (simulateQ (findOracles x.1.2.1) (adv.find x.1.1 pk x.1.2.2)).run [] >>=
        fun z => pure (z.1.1, decide ((x.1.2.1[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨
          z.1.1 ∈ z.2))
      match x.2.challenges[y.1]? with
      | none => pure false
      | some (t, m) => pure (x.2.valid &&
          decide (SecondPreimageExists prob.th pk t m ↔ y.2 = true))) := rfl
  rw [h1]
  unfold raw
  simp only [map_bind, map_pure, red_choose_run, bind_assoc, pure_bind]
  refine bind_congr fun pk => ?_
  refine bind_congr_of_forall_mem_support _ fun w hw => ?_
  have h0 := pick_challenges adv pk w hw
  refine bind_congr fun tg => ?_
  have hc : (recAll prob.numTargets w.2 tg).challenges = tg := by
    rw [recAll_challenges, h0]; rfl
  simp only [hc]
  refine bind_congr fun z => ?_
  obtain ⟨⟨j, m⟩, op⟩ := z
  simp only [pred, cD]
  cases h : tg[j]? with
  | none => rfl
  | some q => simp

theorem sp_experiment_eq [Fintype M] [DecidableEq M] [DecidableEq Y]
    {prob : Problem ι PkSeed Tweak M Y} (adv : Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.spExperiment (toDSPR adv) =
      pred prob.numTargets (cS prob.th) <$> raw adv := by
  have h1 : SM_DT_DSPR_SourceFinalValidity.spExperiment (toDSPR adv) = (do
      let pk ← prob.th.seedGen
      let x ← (simulateQ (redOracles prob pk) (redChoose adv)).run .initial
      let y ← (simulateQ (findOracles x.1.2.1) (adv.find x.1.1 pk x.1.2.2)).run [] >>=
        fun z => pure (z.1.1, decide ((x.1.2.1[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨
          z.1.1 ∈ z.2))
      match x.2.challenges[y.1]? with
      | none => pure false
      | some (t, m) => pure (x.2.valid &&
          decide (SecondPreimageExists prob.th pk t m))) := rfl
  rw [h1]
  unfold raw
  simp only [map_bind, map_pure, red_choose_run, bind_assoc, pure_bind]
  refine bind_congr fun pk => ?_
  refine bind_congr_of_forall_mem_support _ fun w hw => ?_
  have h0 := pick_challenges adv pk w hw
  refine bind_congr fun tg => ?_
  have hc : (recAll prob.numTargets w.2 tg).challenges = tg := by
    rw [recAll_challenges, h0]; rfl
  simp only [hc]
  refine bind_congr fun z => ?_
  obtain ⟨⟨j, m⟩, op⟩ := z
  simp only [pred, cS]
  cases h : tg[j]? with
  | none => rfl
  | some q => rfl

end Reductions

/-! ## The inversion phase does not depend on an unopened hidden input -/

section Invariance

variable [Inhabited M]

/-- Hide the outcome of the inversion phase when target `i` has been opened. -/
def hide (i : ℕ) {α : Type} (z : α × List ℕ) : Option (α × List ℕ) :=
  if i ∈ z.2 then none else some z

theorem find_opened_mono (tg : List (Tweak × M)) (i : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + openSpec M) α) (op0 : List ℕ) (h : i ∈ op0) :
    ∀ z ∈ support ((simulateQ (findOracles tg) oa).run op0), i ∈ z.2 :=
  OracleComp.simulateQ_run_preservesInv (findOracles tg) (fun op => i ∈ op)
    ((SourceFinalValidity.preservesInv_privateRandomness _).add (fun j op hop z hz => by
      rw [openOracle_run, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [hop])) oa op0 h

theorem hide_of_opened (tg : List (Tweak × M)) (i : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + openSpec M) α) (op0 : List ℕ) (h : i ∈ op0) :
    hide i <$> (simulateQ (findOracles tg) oa).run op0 =ᵈ
      (pure none : ProbComp (Option (α × List ℕ))) := by
  have h1 : hide i <$> (simulateQ (findOracles tg) oa).run op0 =
      (fun _ => none) <$> (simulateQ (findOracles tg) oa).run op0 := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine bind_congr_of_forall_mem_support _ fun z hz => ?_
    simp [hide, find_opened_mono tg i oa op0 h z hz]
  rw [h1]
  exact OracleComp.EvalDistEq.map_const _ _

/-- **Run invariance.**  If two target lists give the same opening answers at every index except
`i`, the inversion phase has the same distribution under both, up to runs that open `i`. -/
theorem find_run_congr (tg tg' : List (Tweak × M)) (i : ℕ)
    (hagree : ∀ k, k ≠ i →
      (tg[k]?.map Prod.snd).getD default = (tg'[k]?.map Prod.snd).getD default)
    {α : Type} (oa : OracleComp (unifSpec + openSpec M) α) (op0 : List ℕ) :
    hide i <$> (simulateQ (findOracles tg) oa).run op0 =ᵈ
      hide i <$> (simulateQ (findOracles tg') oa).run op0 := by
  induction oa using OracleComp.inductionOn generalizing op0 with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | j
    · have h1 : ∀ tg : List (Tweak × M), (findOracles tg (.inl n)).run op0 =
          (fun u => (u, op0)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        intro tg; simp [findOracles]
      rw [h1, h1]
      simp only [bind_map_left]
      exact EvalDistEq.bind_right _ fun u => ih u op0
    · have h2 : ∀ tg : List (Tweak × M), (findOracles tg (.inr j)).run op0 =
          pure ((tg[j]?.map Prod.snd).getD default, op0 ++ [j]) := fun tg => openOracle_run
      rw [h2, h2, pure_bind, pure_bind]
      by_cases hj : j = i
      · subst hj
        exact (hide_of_opened tg j _ _ (by simp)).trans (hide_of_opened tg' j _ _ (by simp)).symm
      · rw [hagree j hj]
        exact ih _ _

end Invariance

/-! ## Resampling one hidden input -/

/-- Uniform target sampling is invariant under applying a tweak-indexed bijection to the hidden
input at one position. -/
theorem sampleT_modify [SampleableType M] (σ : Tweak → M → M)
    (hσ : ∀ t, Function.Bijective (σ t)) (i : ℕ) (ts : List Tweak) :
    (fun tg : List (Tweak × M) => tg.modify i (fun q => (q.1, σ q.1 q.2))) <$>
        sampleT ($ᵗ M) ts =ᵈ sampleT ($ᵗ M) ts := by
  induction ts generalizing i with
  | nil => simp only [sampleT, map_pure, List.modify_nil]; exact EvalDistEq.rfl
  | cons t ts ih =>
    cases i with
    | zero =>
      simp only [sampleT, map_bind, map_pure, List.modify_zero_cons]
      have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective (hσ t)).bind_left
        (fun x => sampleT ($ᵗ M) ts >>= fun r => pure ((t, x) :: r))
      rw [bind_map_left] at h
      exact h
    | succ i =>
      simp only [sampleT, map_bind, map_pure, List.modify_succ_cons]
      refine EvalDistEq.bind_right _ fun x => ?_
      have h := (ih i).bind_left (fun r => (pure ((t, x) :: r) : ProbComp _))
      rw [bind_map_left] at h
      exact h

/-- A permutation of a finite type that preserves the fibres of `f` and has no fixed point in any
fibre with at least two elements.  (Used in the proof only; no adversary depends on it.) -/
theorem exists_fibre_shift [Fintype M] [DecidableEq M] [DecidableEq Y] (f : M → Y) :
    ∃ σ : M → M, Function.Bijective σ ∧ (∀ x, f (σ x) = f x) ∧
      ∀ x x', x ≠ x' → f x = f x' → σ x ≠ x := by
  classical
  let fib : M → Finset M := fun x => Finset.univ.filter fun m => f m = f x
  have hmem : ∀ x, x ∈ (fib x).toList := fun x => by simp [fib]
  have hfib : ∀ x y, f x = f y → fib x = fib y := fun x y h => by simp [fib, h]
  let σ : M → M := fun x => (fib x).toList.formPerm x
  have hf : ∀ x, f (σ x) = f x := fun x => by
    have : σ x ∈ (fib x).toList := List.formPerm_apply_mem_of_mem (hmem x)
    simpa [fib] using this
  refine ⟨σ, ?_, hf, ?_⟩
  · refine Function.Injective.bijective_of_finite fun x y h => ?_
    have hxy : f x = f y := by rw [← hf x, ← hf y, h]
    have h' : (fib x).toList.formPerm x = (fib x).toList.formPerm y := by
      have := h; simp only [σ] at this; rwa [← hfib x y hxy] at this
    exact (Equiv.injective _) h'
  · intro x x' hne hfx
    have hlen : 2 ≤ (fib x).toList.length := by
      rw [Finset.length_toList]
      have : 1 < (fib x).card := Finset.one_lt_card.2
        ⟨x, by simp [fib], x', by simp [fib, hfx], hne⟩
      omega
    exact (List.formPerm_apply_mem_ne_self_iff _ (Finset.nodup_toList _) x (hmem x)).2 hlen

/-! ## Probability helpers -/

/-- Monotonicity of the success probability of a Boolean post-processing. -/
theorem prTrue_map_mono {α : Type} (mx : ProbComp α) (f g : α → Bool)
    (h : ∀ a, f a = true → g a = true) : 𝒟[f <$> mx] {true} ≤ 𝒟[g <$> mx] {true} := by
  let _ : MeasurableSpace α := ⊤
  rw [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete),
    evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)]
  exact measure_mono fun a ha => h a ha

theorem prTrue_map_congr {α : Type} {mx my : ProbComp α} (h : mx =ᵈ my) (f : α → Bool) :
    𝒟[f <$> mx] {true} = 𝒟[f <$> my] {true} := by
  rw [(h.map f).evalDist_eq]

/-! ## The key inequality: returning the hidden input is no likelier than a collision -/

section Key

variable [DecidableEq Tweak] [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y]

/-- `E₁`: the adversary returned the hidden input of an unopened target with a second preimage. -/
def cE1 (th : TweakableHash PkSeed Tweak M Y) : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool :=
  fun pk t x j m op => decide (j ∉ op ∧ m = x ∧ SecondPreimageExists th pk t x)

/-- `E₂`: the adversary returned a different preimage of an unopened target. -/
def cE2 (th : TweakableHash PkSeed Tweak M Y) : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool :=
  fun pk t x j m op => decide (j ∉ op ∧ m ≠ x ∧ th.eval pk t m = th.eval pk t x)

omit [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y] in
theorem pred_eq_true_iff (n : ℕ) (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool) (pk : PkSeed)
    (st : State Tweak M) (tg : List (Tweak × M)) (j : ℕ) (m : M) (op : List ℕ) :
    pred n c (pk, st, tg, ((j, m), op)) = true ↔
      ∃ t x, tg[j]? = some (t, x) ∧ (recAll n st tg).valid = true ∧ c pk t x j m op = true := by
  simp only [pred]
  cases h : tg[j]? with
  | none => simp
  | some q => obtain ⟨t, x⟩ := q; simp

/-- Restricting a predicate that requires `j ∉ opened` to `j = i` only looks at runs that do not
open `i`. -/
def predAt (n : ℕ) (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool) (pk : PkSeed)
    (st : State Tweak M) (i : ℕ) (p : List (Tweak × M) × Option ((ℕ × M) × List ℕ)) : Bool :=
  match p.2 with
  | none => false
  | some z => pred n c (pk, st, p.1, z) && decide (z.1.1 = i)

omit [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y] in
theorem pred_and_eq_predAt (n : ℕ) (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool)
    (hc : ∀ pk t x j m op, c pk t x j m op = true → j ∉ op) (pk : PkSeed) (st : State Tweak M)
    (i : ℕ) (tg : List (Tweak × M)) (z : (ℕ × M) × List ℕ) :
    (pred n c (pk, st, tg, z) && decide (z.1.1 = i)) = predAt n c pk st i (tg, hide i z) := by
  obtain ⟨⟨j, m⟩, op⟩ := z
  unfold predAt hide
  by_cases h : i ∈ op
  · simp only [h, ite_true]
    rw [Bool.and_eq_false_iff]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [Bool.not_eq_false] at h1 h2
    obtain ⟨t, x, -, -, h3⟩ := (pred_eq_true_iff n c pk st tg j m op).1 h1
    have : j = i := by simpa using h2
    exact hc pk t x j m op h3 (this ▸ h)
  · simp [h]

omit [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y] [DecidableEq Tweak] in
theorem images_modify (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (σ : Tweak → M → M)
    (hpres : ∀ t x, th.eval pk t (σ t x) = th.eval pk t x) (i : ℕ) (tg : List (Tweak × M)) :
    images th pk (tg.modify i (fun q => (q.1, σ q.1 q.2))) = images th pk tg := by
  induction tg generalizing i with
  | nil => simp
  | cons q tg ih =>
    cases i with
    | zero => simp [images, hpres]
    | succ i =>
      have := ih i
      simp only [images] at this
      simp [images, this]

omit [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y] [DecidableEq Tweak] in
theorem map_fst_modify (σ : Tweak → M → M) (i : ℕ) (tg : List (Tweak × M)) :
    (tg.modify i (fun q => (q.1, σ q.1 q.2))).map Prod.fst = tg.map Prod.fst := by
  induction tg generalizing i with
  | nil => simp
  | cons q tg ih =>
    cases i with
    | zero => simp
    | succ i => simp [ih i]

/-- For a fixed seed, commitment-phase outcome and index `i`: over uniform hidden inputs,
`Pr[E₁ ∧ j = i] ≤ Pr[E₂ ∧ j = i]`. -/
theorem inner_le [SampleableType M] (th : TweakableHash PkSeed Tweak M Y) (n : ℕ) (pk : PkSeed)
    (st : State Tweak M) (i : ℕ) (ts : List Tweak)
    (fnd : List Y → OracleComp (unifSpec + openSpec M) (ℕ × M)) :
    𝒟[sampleT ($ᵗ M) ts >>= fun tg =>
        (simulateQ (findOracles tg) (fnd (images th pk tg))).run [] >>= fun z =>
          pure (pred n (cE1 th) (pk, st, tg, z) && decide (z.1.1 = i))] {true} ≤
      𝒟[sampleT ($ᵗ M) ts >>= fun tg =>
        (simulateQ (findOracles tg) (fnd (images th pk tg))).run [] >>= fun z =>
          pure (pred n (cE2 th) (pk, st, tg, z) && decide (z.1.1 = i))] {true} := by
  choose σ hbij hpres hmove using fun t => exists_fibre_shift (th.eval pk t)
  set φ : List (Tweak × M) → List (Tweak × M) :=
    fun tg => tg.modify i (fun q => (q.1, σ q.1 q.2)) with hφ
  set K : List (Tweak × M) → ProbComp (List (Tweak × M) × Option ((ℕ × M) × List ℕ)) :=
    fun tg => (hide i <$> (simulateQ (findOracles tg) (fnd (images th pk tg))).run []) >>=
      fun w => pure (tg, w) with hK
  set X : ProbComp (List (Tweak × M) × Option ((ℕ × M) × List ℕ)) :=
    sampleT ($ᵗ M) ts >>= K with hX
  have hform : ∀ c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool,
      (∀ pk t x j m op, c pk t x j m op = true → j ∉ op) →
      (sampleT ($ᵗ M) ts >>= fun tg =>
        (simulateQ (findOracles tg) (fnd (images th pk tg))).run [] >>= fun z =>
          pure (pred n c (pk, st, tg, z) && decide (z.1.1 = i))) = predAt n c pk st i <$> X := by
    intro c hc
    simp only [hX, hK, map_bind, map_pure, bind_map_left]
    refine bind_congr fun tg => bind_congr fun z => ?_
    rw [pred_and_eq_predAt n c hc]
  rw [hform (cE1 th) (fun pk t x j m op h => by simp only [cE1, decide_eq_true_eq] at h; exact h.1),
    hform (cE2 th) (fun pk t x j m op h => by simp only [cE2, decide_eq_true_eq] at h; exact h.1)]
  -- resampling coordinate `i`
  have hXφ : X =ᵈ (fun p => (φ p.1, p.2)) <$> X := by
    have h1 : X =ᵈ (φ <$> sampleT ($ᵗ M) ts) >>= K :=
      ((sampleT_modify σ hbij i ts).bind_left K).symm
    refine h1.trans ?_
    rw [bind_map_left]
    simp only [hX, map_bind]
    refine EvalDistEq.bind_right _ fun tg => ?_
    simp only [hK, map_bind, map_pure]
    have himg : images th pk (φ tg) = images th pk tg := images_modify th pk σ hpres i tg
    rw [himg]
    refine (find_run_congr (φ tg) tg i (fun k hk => ?_) _ []).bind_left _
    simp only [hφ, List.getElem?_modify]
    cases tg[k]? with
    | none => rfl
    | some q => simp [Ne.symm hk]
  rw [prTrue_map_congr hXφ, Functor.map_map]
  refine prTrue_map_mono _ _ _ fun p hp => ?_
  obtain ⟨tg, w⟩ := p
  cases w with
  | none => simp [predAt] at hp
  | some z =>
    obtain ⟨⟨j, m⟩, op⟩ := z
    simp only [predAt, Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
    obtain ⟨hp1, hji⟩ := hp
    refine ⟨?_, hji⟩
    obtain ⟨t, x, hget, hval, hc⟩ := (pred_eq_true_iff _ _ _ _ _ _ _ _).1 hp1
    simp only [cE1, decide_eq_true_eq] at hc
    obtain ⟨hop, hmx, hspe⟩ := hc
    subst hji
    simp only [hφ, List.getElem?_modify] at hget
    cases hq : tg[j]? with
    | none => simp [hq] at hget
    | some q =>
      obtain ⟨t0, x0⟩ := q
      simp only [hq, ite_true] at hget
      obtain ⟨rfl, rfl⟩ := hget
      refine (pred_eq_true_iff _ _ _ _ _ _ _ _).2 ⟨t0, x0, hq, ?_, ?_⟩
      · rw [← hval]
        exact recAll_valid_congr n st st _ _ rfl rfl rfl (map_fst_modify σ j tg).symm
      · simp only [cE2, decide_eq_true_eq]
        refine ⟨hop, ?_, ?_⟩
        · rw [hmx]
          obtain ⟨m', hne, heq⟩ := hspe
          by_cases hm' : m' = x0
          · subst hm'; exact hne
          · exact hmove t0 x0 m' (Ne.symm hm') (by rw [← heq, hpres])
        · rw [hmx, hpres]

end Key

/-! ## Assembling -/

section Main

variable [DecidableEq Tweak] [Inhabited M] [Fintype M] [DecidableEq M] [DecidableEq Y]

/-- `Pr[E₁] ≤ Pr[E₂]` for the whole experiment, by summing `inner_le` over the selected index. -/
theorem prE1_le_prE2 [SampleableType M] {prob : Problem ι PkSeed Tweak M Y}
    (hU : prob.HasUniformInputs) (adv : Adversary prob) :
    𝒟[pred prob.numTargets (cE1 prob.th) <$> raw adv] {true} ≤
      𝒟[pred prob.numTargets (cE2 prob.th) <$> raw adv] {true} := by
  have hi : ∀ i : ℕ,
      𝒟[(fun r => pred prob.numTargets (cE1 prob.th) r && decide (r.2.2.2.1.1 = i)) <$> raw adv]
          {true} ≤
        𝒟[(fun r => pred prob.numTargets (cE2 prob.th) r && decide (r.2.2.2.1.1 = i)) <$> raw adv]
          {true} := by
    intro i
    unfold raw
    simp only [map_bind, map_pure]
    refine evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.of_discrete) fun pk _ => ?_
    refine evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.of_discrete) fun w _ => ?_
    rw [show prob.inputGen = $ᵗ M from hU]
    exact inner_le prob.th prob.numTargets pk w.2 i (w.1.2.take prob.numTargets)
      (adv.find w.1.1 pk)
  let _ : MeasurableSpace (Raw PkSeed Tweak M) := ⊤
  have hset : ∀ (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool) (i : ℕ),
      𝒟[(fun r => pred prob.numTargets c r && decide (r.2.2.2.1.1 = i)) <$> raw adv] {true} =
        𝒟[raw adv] (pred prob.numTargets c ⁻¹' {true} ∩ {r | r.2.2.2.1.1 = i}) := by
    intro c i
    rw [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)]
    congr 1
    ext r
    simp
  rw [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete),
    evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)]
  calc 𝒟[raw adv] (pred prob.numTargets (cE1 prob.th) ⁻¹' {true})
      ≤ 𝒟[raw adv] (⋃ i : ℕ, pred prob.numTargets (cE1 prob.th) ⁻¹' {true} ∩
          {r | r.2.2.2.1.1 = i}) :=
        measure_mono fun r hr => Set.mem_iUnion.2 ⟨r.2.2.2.1.1, hr, rfl⟩
    _ ≤ ∑' i : ℕ, 𝒟[raw adv] (pred prob.numTargets (cE1 prob.th) ⁻¹' {true} ∩
          {r | r.2.2.2.1.1 = i}) := measure_iUnion_le _
    _ ≤ ∑' i : ℕ, 𝒟[raw adv] (pred prob.numTargets (cE2 prob.th) ⁻¹' {true} ∩
          {r | r.2.2.2.1.1 = i}) :=
        tsum_le_tsum fun i => by rw [← hset, ← hset]; exact hi i
    _ = 𝒟[raw adv] (⋃ i : ℕ, pred prob.numTargets (cE2 prob.th) ⁻¹' {true} ∩
          {r | r.2.2.2.1.1 = i}) := by
        refine (measure_iUnion ?_ fun i => MeasurableSet.of_discrete).symm
        intro i i' hne
        refine Set.disjoint_left.2 fun r hr hr' => hne ?_
        exact hr.2.symm.trans hr'.2
    _ ≤ 𝒟[raw adv] (pred prob.numTargets (cE2 prob.th) ⁻¹' {true}) :=
        measure_mono fun r hr => by
          obtain ⟨i, hi', -⟩ := Set.mem_iUnion.1 hr
          exact hi'

/-- **SM-DT-OpenPRE from SM-DT-DSPR and SM-DT-TCR.**  For every OpenPRE problem with uniform
hidden inputs and **every** OpenPRE adversary `adv`,

`Adv^{OpenPRE}(adv) ≤ (Pr[DSPR(toDSPR adv)] − Pr[SPprob(toDSPR adv)]) + 3 · Adv^{TCR}(toTCR adv)`.

`toDSPR adv` and `toTCR adv` are VCVio's explicit reductions; each runs `adv` once
(`red_choose_run`).  Coefficients as in Hülsing–Kudinov / EasyCrypt `OpenPRE_From_TCR_DSPR_THF`. -/
theorem openPRE_le_dspr_add_three_tcr [SampleableType M] {prob : Problem ι PkSeed Tweak M Y}
    (hU : prob.HasUniformInputs) (adv : Adversary prob) :
    advantage adv ≤
      SM_DT_DSPR_SourceFinalValidity.advantage (toDSPR adv) +
        3 * SM_DT_TCR_SourceFinalValidity.advantage (toTCR adv) := by
  unfold advantage SM_DT_DSPR_SourceFinalValidity.advantage
    SM_DT_DSPR_SourceFinalValidity.Success SM_DT_DSPR_SourceFinalValidity.SPProbability
    SM_DT_TCR_SourceFinalValidity.advantage
  rw [experiment_eq, tcr_experiment_eq, dspr_experiment_eq, sp_experiment_eq]
  have hE := prE1_le_prE2 hU adv
  let _ : MeasurableSpace (Raw PkSeed Tweak M) := ⊤
  simp only [evalDist_map_apply_of_discrete _ _ (MeasurableSet.of_discrete)] at hE ⊢
  have hfinμ : IsFiniteMeasure 𝒟[raw adv] := inferInstance
  generalize 𝒟[raw adv] = μ at hE hfinμ ⊢
  set W := pred prob.numTargets (cW prob.th) ⁻¹' {true} with hW
  set S := pred prob.numTargets (cS prob.th) ⁻¹' {true} with hS
  set D := pred prob.numTargets (cD prob.th) ⁻¹' {true} with hD
  set T := pred prob.numTargets (cT prob.th) ⁻¹' {true} with hT
  set E1 := pred prob.numTargets (cE1 prob.th) ⁻¹' {true} with hE1
  set E2 := pred prob.numTargets (cE2 prob.th) ⁻¹' {true} with hE2
  have hmem : ∀ (c : PkSeed → Tweak → M → ℕ → M → List ℕ → Bool) (r : Raw PkSeed Tweak M),
      r ∈ pred prob.numTargets c ⁻¹' {true} ↔
        ∃ t x, r.2.2.1[r.2.2.2.1.1]? = some (t, x) ∧
          (recAll prob.numTargets r.2.1 r.2.2.1).valid = true ∧
          c r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2 = true := by
    rintro c ⟨pk, st, tg, ⟨j, m⟩, op⟩
    exact pred_eq_true_iff _ _ _ _ _ _ _ _
  -- pointwise logic
  have key : ∀ (pk : PkSeed) (t : Tweak) (x : M) (j : ℕ) (m : M) (op : List ℕ),
      (cS prob.th pk t x j m op = true ∨ cW prob.th pk t x j m op = true) →
        cD prob.th pk t x j m op = true ∨ cE1 prob.th pk t x j m op = true := by
    intro pk t x j m op h
    simp only [cS, cW, cD, cE1, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    by_cases hspe : SecondPreimageExists prob.th pk t x
    · by_cases hb : x ≠ m ∨ j ∈ op
      · exact Or.inl ⟨fun _ => hb, fun _ => hspe⟩
      · rw [not_or, not_not] at hb
        exact Or.inr ⟨hb.2, hb.1.symm, hspe⟩
    · rcases h with h | ⟨hop, heq⟩
      · exact absurd h hspe
      · refine Or.inl ⟨fun h' => absurd h' hspe, fun hb => ?_⟩
        rcases hb with hne | hin
        · exact absurd ⟨m, hne, heq.symm⟩ hspe
        · exact absurd hin hop
  have h2 : W ∪ S ⊆ D ∪ E1 := by
    intro r hr
    have : ∃ t x, r.2.2.1[r.2.2.2.1.1]? = some (t, x) ∧
        (recAll prob.numTargets r.2.1 r.2.2.1).valid = true ∧
        (cS prob.th r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2 = true ∨
          cW prob.th r.1 t x r.2.2.2.1.1 r.2.2.2.1.2 r.2.2.2.2 = true) := by
      rcases hr with hr | hr
      · obtain ⟨t, x, h1, h2, h3⟩ := (hmem _ r).1 hr
        exact ⟨t, x, h1, h2, Or.inr h3⟩
      · obtain ⟨t, x, h1, h2, h3⟩ := (hmem _ r).1 hr
        exact ⟨t, x, h1, h2, Or.inl h3⟩
    obtain ⟨t, x, h1, h2, h3⟩ := this
    rcases key _ _ _ _ _ _ h3 with h | h
    · exact Or.inl ((hmem _ r).2 ⟨t, x, h1, h2, h⟩)
    · exact Or.inr ((hmem _ r).2 ⟨t, x, h1, h2, h⟩)
  have h1 : W ∩ S ⊆ T ∪ E1 := by
    intro r hr
    obtain ⟨t, x, hg, hv, hw⟩ := (hmem _ r).1 hr.1
    obtain ⟨t', x', hg', -, hs⟩ := (hmem _ r).1 hr.2
    rw [hg] at hg'
    simp only [Option.some.injEq, Prod.mk.injEq] at hg'
    obtain ⟨rfl, rfl⟩ := hg'
    simp only [cW, cS, Bool.and_eq_true, decide_eq_true_eq] at hw hs
    by_cases hm : r.2.2.2.1.2 = x
    · exact Or.inr ((hmem _ r).2 ⟨t, x, hg, hv, by
        simp only [cE1, decide_eq_true_eq]; exact ⟨hw.1, hm, hs⟩⟩)
    · exact Or.inl ((hmem _ r).2 ⟨t, x, hg, hv, by
        simp only [cT, decide_eq_true_eq]; exact ⟨hm, hw.2⟩⟩)
  have h3 : E2 ⊆ T := by
    intro r hr
    obtain ⟨t, x, hg, hv, hc⟩ := (hmem _ r).1 hr
    simp only [cE2, decide_eq_true_eq] at hc
    exact (hmem _ r).2 ⟨t, x, hg, hv, by simp only [cT, decide_eq_true_eq]; exact hc.2⟩
  have hsum : μ W + μ S ≤ μ D + μ T + 2 * μ E1 :=
    calc μ W + μ S = μ (W ∪ S) + μ (W ∩ S) :=
          (measure_union_add_inter W MeasurableSet.of_discrete).symm
      _ ≤ μ (D ∪ E1) + μ (T ∪ E1) := add_le_add (measure_mono h2) (measure_mono h1)
      _ ≤ (μ D + μ E1) + (μ T + μ E1) :=
          add_le_add (measure_union_le _ _) (measure_union_le _ _)
      _ = μ D + μ T + 2 * μ E1 := by ring
  have hE1T : μ E1 ≤ μ T := hE.trans (measure_mono h3)
  have hfin : μ S ≠ ⊤ := measure_ne_top _ _
  have hfinal : μ W + μ S ≤ (μ D - μ S) + 3 * μ T + μ S :=
    calc μ W + μ S ≤ μ D + μ T + 2 * μ E1 := hsum
      _ ≤ μ D + μ T + 2 * μ T := by gcongr
      _ = μ D + 3 * μ T := by ring
      _ ≤ (μ D - μ S + μ S) + 3 * μ T := by gcongr; exact le_tsub_add
      _ = (μ D - μ S) + 3 * μ T + μ S := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 hfinal

end Main

#print axioms openPRE_le_dspr_add_three_tcr

end Reduction.ForsTight
