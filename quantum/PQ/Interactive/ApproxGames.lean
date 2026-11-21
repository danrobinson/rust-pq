import PQ.Interactive.ApproxLimit
import PQ.Interactive.Games
import PQ.Interactive.EUFCMA

/-!
# Game limits: quantum advantages as limits of classical advantages

For each quantum game of `Games.lean` / `EUFCMA.lean` (defined by Born weights, with no
rationality hypothesis) and every sequence of samplers converging to the Born rule
(`BornApprox samp`, e.g. the rational samplers `sampN`), the classical advantage of the `n`-th
classical approximant of the quantum adversary tends to the quantum advantage:

* `tendsto_prfAdvantage`, `tendsto_itsrAdvantage` (single-stage games);
* `tendsto_SM_DT_TCR_Advantage`, `tendsto_SM_DT_PRE_Advantage`, `tendsto_SM_DT_UD_Advantage`,
  `tendsto_tcrFV_advantage`, `tendsto_dsprFV_advantage` (two-phase games, quantum second phase);
* `tendsto_unforgeableAdvantage`, `tendsto_strongUnforgeableAdvantage` (EUF-CMA / SUF-CMA).

`qUnforgeableAdvantage_le_of_forall_of_tendsto` is the resulting unconditional lifting principle.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Topology
open Filter (Tendsto atTop)
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}
variable {samp : ℕ → Sampler W}

/-! ## Generic facts -/

lemma tendsto_absDiff {a b : ℕ → ℝ≥0∞} {x y : ℝ≥0∞} (ha : Tendsto a atTop (𝓝 x))
    (hb : Tendsto b atTop (𝓝 y)) (hx : x ≠ ∞) (hy : y ≠ ∞) :
    Tendsto (fun n ↦ ENNReal.absDiff (a n) (b n)) atTop (𝓝 (ENNReal.absDiff x y)) := by
  unfold ENNReal.absDiff
  exact (ENNReal.Tendsto.sub ha hb (Or.inl hx)).add (ENNReal.Tendsto.sub hb ha (Or.inl hy))

lemma qWeight_ne_top (p : α → Prop) [DecidablePred p] (X : Closed W α) {ρ : Matrix W W ℂ}
    (hρ : ρ.PosSemidef) : qWeight p X ρ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (qWeight_le_trace p X hρ)

/-- Classical post-processing collapses exactly (no sampling of instrument outcomes). -/
lemma qWeight_liftU (p : β → Prop) [DecidablePred p] (oa : ProbComp β) (ρ : Matrix W W ℂ) :
    qWeight p (liftU oa : Closed W β) ρ = ENNReal.ofReal ρ.trace.re * prob oa p := by
  have := qWeight_liftU_bind p oa (pure : β → Closed W β) pure
    (ENNReal.ofReal ρ.trace.re) ρ (fun x ↦ by simp)
  simpa using this

/-- Limit collapse of an open machine against `impl`, in `prob` form. -/
theorem tendsto_prob_close (hs : BornApprox samp)
    (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (himpl : ForwardsUnif impl)
    (p : α × σ → Prop) [DecidablePred p] (Q : QOC W (unifSpec + spec') α) (s : σ)
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ prob ((simulateQ impl (toProbCompWith (samp n) Q ρ)).run s) p)
      atTop (𝓝 (qWeight p (close impl Q s) ρ)) :=
  tendsto_prEvent_close hs impl himpl p Q s ρ hρ h1

/-- **Limit collapse for single-stage games** (the limit form of `qWeight_game`). -/
theorem tendsto_game (hs : BornApprox samp) (pre : ProbComp γ)
    (impl : γ → QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ∀ a, ForwardsUnif (impl a)) (s₀ : γ → σ) (post : γ → α × σ → ProbComp β)
    (Q : γ → QOC W (unifSpec + spec') α) (p : β → Prop) [DecidablePred p]
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ prob (pre >>= fun a ↦
        (simulateQ (impl a) (toProbCompWith (samp n) (Q a) ρ)).run (s₀ a) >>= post a) p) atTop
      (𝓝 (qWeight p
        (liftU pre >>= fun a ↦ close (impl a) (Q a) (s₀ a) >>= fun r ↦ liftU (post a r)) ρ)) := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  have key : ∀ a, Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob
        ((simulateQ (impl a) (toProbCompWith (samp n) (Q a) ρ)).run (s₀ a) >>= post a) p) atTop
      (𝓝 (qWeight p (close (impl a) (Q a) (s₀ a) >>= fun r ↦ liftU (post a r)) ρ)) := by
    intro a
    rw [← h1']
    refine tendsto_close_bind hs _ (himpl a) p _ (fun _ ↦ post a) (fun r ρ' _ ↦ ?_) _ _ _ hρ
    rw [qWeight_liftU]
    exact tendsto_const_nhds
  have := tendsto_liftU_bind p pre _ _ 1 ρ key
  simp only [one_mul] at this
  exact this

/-- **Limit collapse for two-phase games** (the limit form of `qWeight_twoPhase`). -/
theorem tendsto_twoPhase (hs : BornApprox samp) (pre : ProbComp γ) (X : γ → Closed W α)
    (post : γ → α → ProbComp β) (p : β → Prop) [DecidablePred p] (ρ : Matrix W W ℂ)
    (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ prob (pre >>= fun a ↦ toProbCompCWith (samp n) (X a) ρ >>= post a) p) atTop
      (𝓝 (qWeight p (liftU pre >>= fun a ↦ X a >>= fun x ↦ liftU (post a x)) ρ)) := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  have key : ∀ a, Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob
        (toProbCompCWith (samp n) (X a) ρ >>= post a) p) atTop
      (𝓝 (qWeight p (X a >>= fun x ↦ liftU (post a x)) ρ)) := by
    intro a
    rw [← h1']
    refine tendsto_bind_closed hs p _ (fun _ ↦ post a) (fun x ρ' _ ↦ ?_) _ _ hρ
    rw [qWeight_liftU]
    exact tendsto_const_nhds
  have := tendsto_liftU_bind p pre _ _ 1 ρ key
  simp only [one_mul] at this
  exact this

/-! ## The PRF game -/

section prf

variable {K D R : Type}

theorem tendsto_prfRealExperiment (hs : BornApprox samp) (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ 𝒟[prf.prfRealExperiment (toProbCompWith (samp n) Q ρ)] {true}) atTop
      (𝓝 (qWeight (· = true) (qPrfRealExperiment prf Q) ρ)) := by
  simp only [← prob_eq_evalDist_true]
  have key : ∀ k, Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob
        (simulateQ (prf.prfRealQueryImpl k) (toProbCompWith (samp n) Q ρ)) (· = true)) atTop
      (𝓝 (qWeight (· = true)
        (Prod.fst <$> close (statelessImpl (prf.prfRealQueryImpl k)) Q ()) ρ)) := by
    intro k
    rw [qWeight_map]
    refine (tendsto_prob_close hs _ (forwardsUnif_prfReal prf k) _ Q () ρ hρ h1).congr fun n ↦ ?_
    rw [one_mul, run_simulateQ_statelessImpl, prob_map]
  have := tendsto_liftU_bind (· = true) prf.keygen _ _ 1 ρ key
  simp only [one_mul] at this
  exact this

theorem tendsto_prfIdealExperiment [DecidableEq D] [SampleableType R] (hs : BornApprox samp)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ 𝒟[PRFScheme.prfIdealExperiment (toProbCompWith (samp n) Q ρ)] {true}) atTop
      (𝓝 (qWeight (· = true) (qPrfIdealExperiment Q) ρ)) := by
  simp only [← prob_eq_evalDist_true]
  rw [qPrfIdealExperiment, qWeight_map]
  refine (tendsto_prob_close hs _ forwardsUnif_prfIdeal _ Q ∅ ρ hρ h1).congr fun n ↦ ?_
  rw [PRFScheme.prfIdealExperiment, StateT.run'_eq, prob_map]

/-- **The quantum PRF advantage is the limit of the classical PRF advantages of the
approximants.** -/
theorem tendsto_prfAdvantage [DecidableEq D] [SampleableType R] (hs : BornApprox samp)
    (prf : PRFScheme K D R) (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ)
    (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ prf.prfAdvantage (toProbCompWith (samp n) Q ρ)) atTop
      (𝓝 (qPrfAdvantage prf Q ρ)) :=
  tendsto_absDiff (tendsto_prfRealExperiment hs prf Q ρ hρ h1)
    (tendsto_prfIdealExperiment hs Q ρ hρ h1) (qWeight_ne_top _ _ hρ) (qWeight_ne_top _ _ hρ)

end prf

/-! ## The ITSR game -/

section itsr

open KeyedHash

variable {K X Y Index : Type}

/-- **The quantum ITSR advantage is the limit of the classical ITSR advantages of the
approximants.** -/
theorem tendsto_itsrAdvantage [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (hs : BornApprox samp) (prob : ITSRProblem K X Y Index)
    (Q : QOC W (unifSpec + ITSRTargetSpec X K) (K × X)) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ ITSRAdvantage (prob := prob) ⟨toProbCompWith (samp n) Q ρ⟩) atTop
      (𝓝 (qItsrAdvantage prob Q ρ)) := by
  have hf : ForwardsUnif (ITSROracles prob) := forwardsUnif_ofLift_add _
  exact tendsto_prEvent_close hs _ hf
    (fun z : (K × X) × ITSRTranscript K X ↦ prob.Wins z.2 z.1) Q [] ρ hρ h1

end itsr

/-! ## Two-phase games -/

section smtcr

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- The classical adversary whose second phase is the classical strategy of the quantum second
phase for the sampler `s`. -/
noncomputable def QSM_DT_TCR_Adversary.toClassicalWith (s : Sampler W)
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P) :
    SM_DT_TCR_Adversary P where
  State := adv.State
  choose := adv.choose
  forge st pk := toProbCompCWith s (adv.forge st pk) adv.ρ₀

/-- **Quantum SM-DT-TCR advantage = limit of the classical SM-DT-TCR advantages of the
approximants.** -/
theorem tendsto_SM_DT_TCR_Advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_TCR_Advantage (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_TCR_Advantage adv)) := by
  have h1 : ENNReal.ofReal adv.ρ₀.trace.re = 1 := by simp [adv.trace_eq_one]
  rw [qSM_DT_TCR_Advantage, qSM_DT_TCR_Experiment]
  have key : ∀ pk (r : adv.State × SM_DT_TCR_State Tweak M),
      Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob
        (toProbCompCWith (samp n) (adv.forge r.1 pk) adv.ρ₀ >>= fun jm ↦
        (match r.2.1[jm.1]? with
        | none => pure false
        | some tm => pure (decide (jm.2 ≠ tm.2 ∧
            P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool))
        (· = true)) atTop
      (𝓝 (qWeight (· = true) (adv.forge r.1 pk >>= fun jm ↦
        (match r.2.1[jm.1]? with
        | none => pure false
        | some tm => pure (decide (jm.2 ≠ tm.2 ∧
            P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : Closed W Bool)) adv.ρ₀)) := by
    intro pk r
    have hfg : ∀ (jm : ℕ × M) (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
        Tendsto (fun _ : ℕ ↦ ENNReal.ofReal ρ'.trace.re * prob
          (match r.2.1[jm.1]? with
          | none => pure false
          | some tm => pure (decide (jm.2 ≠ tm.2 ∧
              P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool) (· = true)) atTop
        (𝓝 (qWeight (· = true)
          (match r.2.1[jm.1]? with
          | none => pure false
          | some tm => pure (decide (jm.2 ≠ tm.2 ∧
              P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : Closed W Bool) ρ')) := by
      intro jm ρ' _
      cases r.2.1[jm.1]? <;> simp
    have := tendsto_bind_closed hs (· = true) _ _ hfg (adv.forge r.1 pk) adv.ρ₀ adv.posSemidef
    rw [h1] at this
    exact this
  have step : Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob (P.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_TCR_oracles P pk) adv.choose).run ([], []) >>= fun r ↦
          toProbCompCWith (samp n) (adv.forge r.1 pk) adv.ρ₀ >>= fun jm ↦
            (match r.2.1[jm.1]? with
            | none => pure false
            | some tm => pure (decide (jm.2 ≠ tm.2 ∧
                P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool))
        (· = true)) atTop
      (𝓝 (qWeight (· = true)
      (liftU P.th.seedGen >>= fun pk ↦
        liftU ((simulateQ (SM_DT_TCR_oracles P pk) adv.choose).run ([], [])) >>= fun r ↦
          adv.forge r.1 pk >>= fun jm ↦
            (match r.2.1[jm.1]? with
            | none => pure false
            | some tm => pure (decide (jm.2 ≠ tm.2 ∧
                P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : Closed W Bool))
      adv.ρ₀)) :=
    tendsto_liftU_bind _ _ _ _ _ _ fun pk ↦ tendsto_liftU_bind _ _ _ _ _ _ fun r ↦ key pk r
  refine step.congr fun n ↦ ?_
  rw [one_mul, SM_DT_TCR_Advantage, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_TCR_Experiment
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨st, qs, tw⟩ := r
  refine bind_congr fun jm ↦ ?_
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases qs[j]? with
  | none => rfl
  | some tm => rfl

end smtcr

section smpre

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type}

/-- The classical adversary with the `s`-strategy of the quantum second phase. -/
noncomputable def QSM_DT_PRE_Adversary.toClassicalWith (s : Sampler W)
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_Adversary W P) :
    SM_DT_PRE_Adversary P where
  State := adv.State
  choose := adv.choose
  invert st pk := toProbCompCWith s (adv.invert st pk) adv.ρ₀

/-- **Quantum SM-DT-PRE advantage = limit of the classical SM-DT-PRE advantages of the
approximants.** -/
theorem tendsto_SM_DT_PRE_Advantage [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    (hs : BornApprox samp) {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_PRE_Advantage (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_PRE_Advantage adv)) := by
  rw [qSM_DT_PRE_Advantage, qSM_DT_PRE_Experiment]
  refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
  rw [SM_DT_PRE_Advantage, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_PRE_Experiment
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨st, qs, tw⟩ := r
  refine bind_congr fun jm ↦ ?_
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases qs[j]? with
  | none => rfl
  | some tm => rfl

end smpre

section smud

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type}

/-- The classical adversary with the `s`-strategy of the quantum second phase. -/
noncomputable def QSM_DT_UD_Adversary.toClassicalWith (s : Sampler W)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    SM_DT_UD_Adversary P where
  State := adv.State
  pick := adv.pick
  distinguish st pk := toProbCompCWith s (adv.distinguish st pk) adv.ρ₀

theorem tendsto_SM_DT_UD_Experiment [DecidableEq Tweak] (hs : BornApprox samp)
    (world : SM_DT_UD_World) {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_Adversary W P) :
    Tendsto (fun n ↦ 𝒟[SM_DT_UD_Experiment world (adv.toClassicalWith (samp n))] {true}) atTop
      (𝓝 (qWeight (· = true) (qSM_DT_UD_Experiment world adv) adv.ρ₀)) := by
  rw [qSM_DT_UD_Experiment]
  refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
  rw [← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_UD_Experiment
  simp only [bind_assoc, pure_bind, bind_pure]
  rfl

/-- **Quantum SM-DT-UD advantage = limit of the classical SM-DT-UD advantages of the
approximants.** -/
theorem tendsto_SM_DT_UD_Advantage [DecidableEq Tweak] (hs : BornApprox samp)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_UD_Advantage (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qSM_DT_UD_Advantage adv)) :=
  tendsto_absDiff (tendsto_SM_DT_UD_Experiment hs .real adv)
    (tendsto_SM_DT_UD_Experiment hs .ideal adv) (qWeight_ne_top _ _ adv.posSemidef)
    (qWeight_ne_top _ _ adv.posSemidef)

end smud

section tcrfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- The classical adversary with the `s`-strategy of the quantum second phase. -/
noncomputable def QTcrFV_Adversary.toClassicalWith (s : Sampler W)
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) : SM_DT_TCR_SourceFinalValidity.Adversary P where
  State := adv.State
  choose := adv.choose
  forge st pk := toProbCompCWith s (adv.forge st pk) adv.ρ₀

/-- **Quantum = limit of classical (of the approximants) for source-final-validity
SM-DT-TCR.** -/
theorem tendsto_tcrFV_advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_TCR_SourceFinalValidity.advantage (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qTcrFV_Advantage adv)) := by
  rw [qTcrFV_Advantage, qTcrFV_Experiment]
  refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
  rw [SM_DT_TCR_SourceFinalValidity.advantage, ← prob_eq_evalDist_true]
  congr 1
  unfold SM_DT_TCR_SourceFinalValidity.experiment
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
  obtain ⟨st, gs⟩ := r
  refine bind_congr fun jm ↦ ?_
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases gs.challenges[j]? with
  | none => rfl
  | some tm => rfl

end tcrfv

section dsprfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- The classical adversary with the `s`-strategy of the quantum second phase. -/
noncomputable def QDsprFV_Adversary.toClassicalWith (s : Sampler W)
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : SM_DT_DSPR_SourceFinalValidity.Adversary P where
  State := adv.State
  choose := adv.choose
  guess st pk := toProbCompCWith s (adv.guess st pk) adv.ρ₀

/-- **Quantum = limit of classical (of the approximants) for source-final-validity
SM-DT-DSPR** (truncated difference `Pr[DSPR] - Pr[SPprob]`). -/
theorem tendsto_dsprFV_advantage [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    (hs : BornApprox samp) {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.advantage (adv.toClassicalWith (samp n)))
      atTop (𝓝 (qDsprFV_Advantage adv)) := by
  have h1 : Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.Success
        (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qWeight (· = true) (qDsprFV_Experiment adv) adv.ρ₀)) := by
    rw [qDsprFV_Experiment]
    refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
    rw [SM_DT_DSPR_SourceFinalValidity.Success, ← prob_eq_evalDist_true]
    congr 1
    unfold SM_DT_DSPR_SourceFinalValidity.experiment
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
    obtain ⟨st, gs⟩ := r
    refine bind_congr fun jb ↦ ?_
    obtain ⟨j, b⟩ := jb
    dsimp only
    cases gs.challenges[j]? with
    | none => rfl
    | some tm => rfl
  have h2 : Tendsto (fun n ↦ SM_DT_DSPR_SourceFinalValidity.SPProbability
        (adv.toClassicalWith (samp n))) atTop
      (𝓝 (qWeight (· = true) (qDsprFV_SpExperiment adv) adv.ρ₀)) := by
    rw [qDsprFV_SpExperiment]
    refine (tendsto_twoPhase hs _ _ _ _ _ adv.posSemidef adv.trace_eq_one).congr fun n ↦ ?_
    rw [SM_DT_DSPR_SourceFinalValidity.SPProbability, ← prob_eq_evalDist_true]
    congr 1
    unfold SM_DT_DSPR_SourceFinalValidity.spExperiment
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun pk ↦ bind_congr fun r ↦ ?_
    obtain ⟨st, gs⟩ := r
    refine bind_congr fun jb ↦ ?_
    obtain ⟨j, b⟩ := jb
    dsimp only
    cases gs.challenges[j]? with
    | none => rfl
    | some tm => rfl
  exact ENNReal.Tendsto.sub h1 h2 (Or.inl (qWeight_ne_top _ _ adv.posSemidef))

end dsprfv

/-! ## EUF-CMA and SUF-CMA -/

section eufcma

variable {M PK SK S : Type} {sigAlg : SignatureAlg ProbComp M PK SK S}

/-- The classical forger simulating the quantum forger with the sampler `s`. -/
noncomputable def QForger.toClassicalWith (s : Sampler W) (Q : QForger W sigAlg) :
    SignatureAlg.UnforgeableAdversary sigAlg :=
  ⟨fun pk ↦ toProbCompWith s (Q.main pk) Q.ρ₀⟩

/-- The same classical strategy as a SUF-CMA adversary. -/
noncomputable def QForger.toClassicalStrongWith (s : Sampler W) (Q : QForger W sigAlg) :
    SignatureAlg.StrongUnforgeableAdversary sigAlg :=
  ⟨fun pk ↦ toProbCompWith s (Q.main pk) Q.ρ₀⟩

/-- The `n`-th classical approximant of the quantum forger `Q` (rational sampler `sampN n`). -/
noncomputable abbrev QForger.toClassicalN (n : ℕ) (Q : QForger W sigAlg) :
    SignatureAlg.UnforgeableAdversary sigAlg :=
  Q.toClassicalWith (sampN n)

/-- The signature game against a quantum forger is the limit of the classical games against its
classical approximants. -/
theorem tendsto_qSigExperiment (hs : BornApprox samp)
    (fresh : QueryLog (M →ₒ S) → M → S → Bool) (Q : QForger W sigAlg) :
    Tendsto (fun n ↦ prob (sigAlg.keygen >>= fun ks ↦
        sigAlg.runWithSigningOracle ks.1 ks.2 (toProbCompWith (samp n) (Q.main ks.1) Q.ρ₀) >>=
          fun r ↦ sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun verified ↦
            pure (fresh r.2 r.1.1 r.1.2 && verified)) (· = true)) atTop
      (𝓝 (qWeight (· = true) (qSigExperiment fresh Q) Q.ρ₀)) := by
  have h1 : ENNReal.ofReal Q.ρ₀.trace.re = 1 := by simp [Q.trace_eq_one]
  have key : ∀ ks : PK × SK, Tendsto (fun n ↦ (1 : ℝ≥0∞) * prob
        (sigAlg.runWithSigningOracle ks.1 ks.2 (toProbCompWith (samp n) (Q.main ks.1) Q.ρ₀) >>=
          fun r ↦ sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun verified ↦
            pure (fresh r.2 r.1.1 r.1.2 && verified)) (· = true)) atTop
      (𝓝 (qWeight (· = true)
        (close (signImpl sigAlg ks.1 ks.2) (Q.main ks.1) [] >>= fun r ↦
          liftU (sigAlg.verify ks.1 r.1.1 r.1.2) >>= fun verified ↦
            (pure (fresh r.2 r.1.1 r.1.2 && verified) : Closed W Bool)) Q.ρ₀)) := by
    intro ks
    have hrun : ∀ n, sigAlg.runWithSigningOracle ks.1 ks.2
          (toProbCompWith (samp n) (Q.main ks.1) Q.ρ₀) =
        (simulateQ (signImpl sigAlg ks.1 ks.2)
          (toProbCompWith (samp n) (Q.main ks.1) Q.ρ₀)).run [] := fun n ↦ by
      rw [run_simulateQ_signImpl]
      simp
    have hfg : ∀ (r : (M × S) × QueryLog (M →ₒ S)) (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
        Tendsto (fun _ : ℕ ↦ ENNReal.ofReal ρ'.trace.re * prob
          (sigAlg.verify ks.1 r.1.1 r.1.2 >>= fun verified ↦
            pure (fresh r.2 r.1.1 r.1.2 && verified)) (· = true)) atTop
        (𝓝 (qWeight (· = true)
          (liftU (sigAlg.verify ks.1 r.1.1 r.1.2) >>= fun verified ↦
            (pure (fresh r.2 r.1.1 r.1.2 && verified) : Closed W Bool)) ρ')) := by
      intro r ρ' _
      rw [qWeight_liftU_bind (W := W) (· = true) (sigAlg.verify ks.1 r.1.1 r.1.2) _
        (fun verified ↦ pure (fresh r.2 r.1.1 r.1.2 && verified))
        (ENNReal.ofReal ρ'.trace.re) ρ' (fun v ↦ by simp)]
      exact tendsto_const_nhds
    have := tendsto_close_bind hs _ (forwardsUnif_signImpl sigAlg ks.1 ks.2) (· = true) _ _ hfg
      (Q.main ks.1) [] Q.ρ₀ Q.posSemidef
    rw [h1] at this
    simp only [hrun]
    exact this
  have := tendsto_liftU_bind (· = true) sigAlg.keygen _ _ 1 Q.ρ₀ key
  simp only [one_mul] at this
  exact this

/-- **Quantum EUF-CMA advantage = limit of the classical EUF-CMA advantages of the classical
approximants (L3).**  No hypothesis on the forger. -/
theorem tendsto_unforgeableAdvantage (hs : BornApprox samp) (Q : QForger W sigAlg) :
    Tendsto (fun n ↦ SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (Q.toClassicalWith (samp n))) atTop (𝓝 (qUnforgeableAdvantage Q)) := by
  rw [qUnforgeableAdvantage, qUnforgeableExperiment]
  refine (tendsto_qSigExperiment hs _ Q).congr fun n ↦ ?_
  rw [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rfl

/-- Quantum SUF-CMA advantage = limit of the classical SUF-CMA advantages of the approximants. -/
theorem tendsto_strongUnforgeableAdvantage (hs : BornApprox samp) (Q : QForger W sigAlg) :
    Tendsto (fun n ↦ SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (Q.toClassicalStrongWith (samp n))) atTop (𝓝 (qStrongUnforgeableAdvantage Q)) := by
  rw [qStrongUnforgeableAdvantage, qStrongUnforgeableExperiment]
  refine (tendsto_qSigExperiment hs _ Q).congr fun n ↦ ?_
  rw [SignatureAlg.strongUnforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_singleton]
  rfl

/-- **Unconditional lifting principle.**  If a bound holds for all classical forgers, and the
bound evaluated at the classical approximants of the quantum forger `Q` converges to `b`, then
the quantum EUF-CMA advantage of `Q` is at most `b`.  No rationality hypothesis. -/
theorem qUnforgeableAdvantage_le_of_forall_of_tendsto (Q : QForger W sigAlg)
    (bound : SignatureAlg.UnforgeableAdversary sigAlg → ℝ≥0∞)
    (h : ∀ A, SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ bound A)
    {b : ℝ≥0∞} (hb : Tendsto (fun n ↦ bound (Q.toClassicalN n)) atTop (𝓝 b)) :
    qUnforgeableAdvantage Q ≤ b :=
  le_of_forall_classical_of_tendsto h (fun n ↦ Q.toClassicalN n)
    (tendsto_unforgeableAdvantage bornApprox_sampN Q) hb

end eufcma

end PQ.Interactive

open PQ.Interactive in
#print axioms tendsto_prfAdvantage
open PQ.Interactive in
#print axioms tendsto_itsrAdvantage
open PQ.Interactive in
#print axioms tendsto_SM_DT_TCR_Advantage
open PQ.Interactive in
#print axioms tendsto_SM_DT_PRE_Advantage
open PQ.Interactive in
#print axioms tendsto_SM_DT_UD_Advantage
open PQ.Interactive in
#print axioms tendsto_tcrFV_advantage
open PQ.Interactive in
#print axioms tendsto_dsprFV_advantage
open PQ.Interactive in
#print axioms tendsto_unforgeableAdvantage
open PQ.Interactive in
#print axioms tendsto_strongUnforgeableAdvantage
open PQ.Interactive in
#print axioms qUnforgeableAdvantage_le_of_forall_of_tendsto
