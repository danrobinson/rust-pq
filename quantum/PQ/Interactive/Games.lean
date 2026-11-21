import PQ.Interactive.Closed
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity

/-!
# Quantum versions of single-stage games

A *single-stage game* is given by classical pre-processing, a stateful classical oracle
implementation run against one adversary program, and classical post-processing.  Its quantum
version replaces the adversary by a quantum machine with classical oracle access and takes Born
weights (`qWeight`/`close`); `qWeight_game` is the collapse theorem for this shape.

Instances:

* the PRF game of VCVio (`PRFScheme.prfAdvantage`): `qPrfAdvantage` and `qPrfAdvantage_eq`;
* the ITSR game (`KeyedHash.ITSRAdvantage`): `qItsrAdvantage` and `qItsrAdvantage_eq`;
* the two-phase SM-DT-TCR game (`TweakableHash.SM_DT_TCR_Advantage`) for adversaries whose first
  phase (target selection, seed hidden) is classical and whose second phase (seed revealed, no
  oracle) is a quantum machine: `qSM_DT_TCR_Advantage` and `qSM_DT_TCR_Advantage_eq`;
* likewise SM-DT-PRE (`qSM_DT_PRE_Advantage_eq`) and SM-DT-UD (`qSM_DT_UD_Advantage_eq`), via the
  generic two-phase collapse `qWeight_twoPhase`;
* the source-final-validity games SM-DT-TCR (`qTcrFV_Advantage_eq`) and SM-DT-DSPR
  (`qDsprFV_Advantage_eq`).
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}

/-! ## Generic facts -/

lemma prob_map {κ : Type} {cs : OracleSpec κ} [OracleSpec.AnswerMeasure cs]
    (mx : OracleComp cs α) (f : α → β) (p : β → Prop) :
    prob (f <$> mx) p = prob mx fun x ↦ p (f x) :=
  prEvent_map mx f p

lemma prob_eq_evalDist_true (mx : ProbComp Bool) : prob mx (· = true) = 𝒟[mx] {true} :=
  prEvent_eq_evalDist_singleton mx true

/-- "Forward uniform sampling + `impl'`" (written with `QueryImpl.ofLift`) forwards uniform
sampling. -/
lemma forwardsUnif_ofLift_add (impl' : QueryImpl spec' (StateT σ ProbComp)) :
    ForwardsUnif ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl') := by
  intro n s
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
  rfl

/-- "Forward uniform sampling + `impl'`" (written with `unifSpec.passthrough`) forwards uniform
sampling. -/
lemma forwardsUnif_passthrough_add (impl' : QueryImpl spec' (StateT σ ProbComp)) :
    ForwardsUnif (unifSpec.passthrough + impl') := by
  intro n s
  simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    QueryImpl.id'_apply]
  rfl

/-- A stateless implementation as a stateful one. -/
def statelessImpl {κ : Type} {cs : OracleSpec κ} (impl : QueryImpl cs ProbComp) :
    QueryImpl cs (StateT Unit ProbComp) :=
  fun t s ↦ (fun u ↦ (u, s)) <$> impl t

lemma run_simulateQ_statelessImpl {κ : Type} {cs : OracleSpec κ} (impl : QueryImpl cs ProbComp)
    (A : OracleComp cs α) (s : Unit) :
    (simulateQ (statelessImpl impl) A).run s = (fun u ↦ (u, s)) <$> simulateQ impl A := by
  induction A using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
      simulateQ_spec_query]
    change ((fun u ↦ (u, s)) <$> impl t) >>= _ = _
    simp [ih]

/-- **Collapse for single-stage games.**  Classical pre-processing `pre`, the quantum machine
`Q a` run against the classical implementation `impl a` from the state `s₀ a`, classical
post-processing `post a`: the Born weight of an event equals its probability in the same game
played by the classical strategy of `Q`. -/
theorem qWeight_game (pre : ProbComp γ)
    (impl : γ → QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ∀ a, ForwardsUnif (impl a)) (s₀ : γ → σ) (post : γ → α × σ → ProbComp β)
    (Q : γ → QOC W (unifSpec + spec') α) (p : β → Prop) [DecidablePred p]
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) (hQ : ∀ a, RationalBorn (Q a) ρ) :
    qWeight p (liftU pre >>= fun a ↦ close (impl a) (Q a) (s₀ a) >>= fun r ↦ liftU (post a r)) ρ =
      prob (pre >>= fun a ↦
        (simulateQ (impl a) (toProbComp (Q a) ρ)).run (s₀ a) >>= post a) p := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  rw [← one_mul (prob _ _)]
  refine qWeight_liftU_bind _ _ _ _ _ _ fun a ↦ ?_
  rw [← h1']
  refine qWeight_close_bind _ (himpl a) _ _ _ (fun r ρ' _ ↦ ?_) _ _ _ hρ (hQ a)
  have := qWeight_liftU_bind p (post a r) (pure : β → Closed W β) pure
    (ENNReal.ofReal ρ'.trace.re) ρ' (fun x ↦ by simp)
  simpa using this

/-! ## The PRF game -/

section prf

variable {K D R : Type}

/-- The real PRF experiment against a quantum distinguisher: sample a key, answer the function
queries of the machine by `prf.eval k`. -/
def qPrfRealExperiment (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) : Closed W Bool :=
  liftU prf.keygen >>= fun k ↦
    Prod.fst <$> close (statelessImpl (prf.prfRealQueryImpl k)) Q ()

/-- The ideal PRF experiment against a quantum distinguisher: answer the function queries of the
machine by VCVio's lazy random function. -/
def qPrfIdealExperiment [DecidableEq D] [SampleableType R]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) : Closed W Bool :=
  Prod.fst <$> close (PRFScheme.prfIdealQueryImpl (D := D) (R := R)) Q ∅

/-- Quantum PRF advantage: the distance between the Born probabilities of output `true` in the
real and the ideal experiment. -/
noncomputable def qPrfAdvantage [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) : ℝ≥0∞ :=
  ENNReal.absDiff (qWeight (· = true) (qPrfRealExperiment prf Q) ρ)
    (qWeight (· = true) (qPrfIdealExperiment Q) ρ)

lemma forwardsUnif_prfReal (prf : PRFScheme K D R) (k : K) :
    ForwardsUnif (statelessImpl (prf.prfRealQueryImpl k)) := by
  intro n s
  simp only [PRFScheme.prfRealQueryImpl, QueryImpl.passthrough_add]
  rfl

lemma forwardsUnif_prfIdeal [DecidableEq D] [SampleableType R] :
    ForwardsUnif (PRFScheme.prfIdealQueryImpl (D := D) (R := R)) :=
  forwardsUnif_passthrough_add _

theorem qWeight_qPrfRealExperiment (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qWeight (· = true) (qPrfRealExperiment prf Q) ρ =
      𝒟[prf.prfRealExperiment (toProbComp Q ρ)] {true} := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  rw [← prob_eq_evalDist_true, ← one_mul (prob _ _)]
  refine qWeight_liftU_bind _ _ _ _ _ _ fun k ↦ ?_
  rw [qWeight_map, qWeight_close_eq_mul _ (forwardsUnif_prfReal prf k) _ Q () ρ hρ hQ,
    run_simulateQ_statelessImpl, prob_map, h1']

theorem qWeight_qPrfIdealExperiment [DecidableEq D] [SampleableType R]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qWeight (· = true) (qPrfIdealExperiment Q) ρ =
      𝒟[PRFScheme.prfIdealExperiment (toProbComp Q ρ)] {true} := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  rw [← prob_eq_evalDist_true, qPrfIdealExperiment, qWeight_map,
    qWeight_close_eq_mul _ forwardsUnif_prfIdeal _ Q ∅ ρ hρ hQ, h1', one_mul,
    PRFScheme.prfIdealExperiment, StateT.run'_eq, prob_map]

/-- **Quantum PRF advantage = classical PRF advantage of the classical strategy.** -/
theorem qPrfAdvantage_eq [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qPrfAdvantage prf Q ρ = prf.prfAdvantage (toProbComp Q ρ) := by
  rw [qPrfAdvantage, qWeight_qPrfRealExperiment prf Q ρ hρ h1 hQ,
    qWeight_qPrfIdealExperiment Q ρ hρ h1 hQ]
  rfl

end prf

/-! ## The ITSR game -/

section itsr

open KeyedHash

variable {K X Y Index : Type}

/-- Quantum ITSR advantage: the machine is run against the target oracle of VCVio's ITSR game
(each query is answered by a fresh key and recorded); it wins if its candidate satisfies the
ITSR relation against the recorded targets. -/
noncomputable def qItsrAdvantage [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (prob : ITSRProblem K X Y Index) (Q : QOC W (unifSpec + ITSRTargetSpec X K) (K × X))
    (ρ : Matrix W W ℂ) : ℝ≥0∞ :=
  qWeight (fun z : (K × X) × ITSRTranscript K X ↦ prob.Wins z.2 z.1)
    (close (ITSROracles prob) Q []) ρ

/-- **Quantum ITSR advantage = classical ITSR advantage of the classical strategy.** -/
theorem qItsrAdvantage_eq [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (prob : ITSRProblem K X Y Index) (Q : QOC W (unifSpec + ITSRTargetSpec X K) (K × X))
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qItsrAdvantage prob Q ρ = ITSRAdvantage (prob := prob) ⟨toProbComp Q ρ⟩ := by
  have hf : ForwardsUnif (ITSROracles prob) := forwardsUnif_ofLift_add _
  rw [qItsrAdvantage, qWeight_close_eq _ hf _ Q [] ρ hρ h1 hQ]
  rfl

end itsr

/-! ## The two-phase SM-DT-TCR game, quantum second phase -/

section smtcr

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- An SM-DT-TCR adversary whose `choose` phase is classical and whose `forge` phase is a quantum
machine (a closed machine: after the seed is revealed there is no oracle).  The state passed
between the phases is classical; the workspace starts in `ρ₀` in the second phase. -/
structure QSM_DT_TCR_Adversary (W : Type) [Fintype W]
    (P : SM_DT_TCR_Problem ι PkSeed Tweak M Y) where
  /-- Classical state carried from `choose` to `forge`. -/
  State : Type
  /-- Classical target selection, as in `SM_DT_TCR_Adversary.choose`. -/
  choose : OracleComp
    (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  forge : State → PkSeed → Closed W (ℕ × M)
  /-- Initial workspace state of the second phase. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The classical adversary with the classical strategy of the quantum second phase. -/
noncomputable def QSM_DT_TCR_Adversary.toClassical {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_Adversary W P) : SM_DT_TCR_Adversary P where
  State := adv.State
  choose := adv.choose
  forge st pk := toProbCompC (adv.forge st pk) adv.ρ₀

/-- The SM-DT-TCR experiment (`SM_DT_TCR_Experiment`) with a quantum second phase. -/
noncomputable def qSM_DT_TCR_Experiment [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P) :
    Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    liftU ((simulateQ (SM_DT_TCR_oracles P pk) adv.choose).run ([], [])) >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2))

/-- Quantum SM-DT-TCR advantage. -/
noncomputable def qSM_DT_TCR_Advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_TCR_Experiment adv) adv.ρ₀

/-- **Quantum SM-DT-TCR advantage = classical SM-DT-TCR advantage of the classical strategy.** -/
theorem qSM_DT_TCR_Advantage_eq [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P)
    (hQ : ∀ st pk, RationalBorn (adv.forge st pk) adv.ρ₀) :
    qSM_DT_TCR_Advantage adv = SM_DT_TCR_Advantage adv.toClassical := by
  have h1 : ENNReal.ofReal adv.ρ₀.trace.re = 1 := by simp [adv.trace_eq_one]
  rw [qSM_DT_TCR_Advantage, SM_DT_TCR_Advantage, ← prob_eq_evalDist_true, qSM_DT_TCR_Experiment]
  have key : ∀ pk (r : adv.State × SM_DT_TCR_State Tweak M),
      qWeight (· = true) (adv.forge r.1 pk >>= fun jm ↦
        (match r.2.1[jm.1]? with
        | none => pure false
        | some tm => pure (decide (jm.2 ≠ tm.2 ∧
            P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : Closed W Bool)) adv.ρ₀ =
      (1 : ℝ≥0∞) * prob (toProbCompC (adv.forge r.1 pk) adv.ρ₀ >>= fun jm ↦
        (match r.2.1[jm.1]? with
        | none => pure false
        | some tm => pure (decide (jm.2 ≠ tm.2 ∧
            P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool))
        (· = true) := by
    intro pk r
    rw [← h1]
    refine qWeight_bind_closed _ _ _ (fun jm ρ' _ ↦ ?_) _ _ adv.posSemidef (hQ r.1 pk)
    cases r.2.1[jm.1]? <;> simp
  have step : qWeight (· = true)
      (liftU P.th.seedGen >>= fun pk ↦
        liftU ((simulateQ (SM_DT_TCR_oracles P pk) adv.choose).run ([], [])) >>= fun r ↦
          adv.forge r.1 pk >>= fun jm ↦
            (match r.2.1[jm.1]? with
            | none => pure false
            | some tm => pure (decide (jm.2 ≠ tm.2 ∧
                P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : Closed W Bool))
      adv.ρ₀ =
      (1 : ℝ≥0∞) * prob (P.th.seedGen >>= fun pk ↦
        (simulateQ (SM_DT_TCR_oracles P pk) adv.choose).run ([], []) >>= fun r ↦
          toProbCompC (adv.forge r.1 pk) adv.ρ₀ >>= fun jm ↦
            (match r.2.1[jm.1]? with
            | none => pure false
            | some tm => pure (decide (jm.2 ≠ tm.2 ∧
                P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)) : ProbComp Bool))
        (· = true) :=
    qWeight_liftU_bind _ _ _ _ _ _ fun pk ↦ qWeight_liftU_bind _ _ _ _ _ _ fun r ↦ key pk r
  rw [step, one_mul]
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

/-! ## Two-phase games with a quantum second phase, generically -/

/-- **Collapse for two-phase games.**  A classical first phase `pre` (everything up to the point
where the quantum machine starts: sampling, the classical phase run inside the game), a quantum
second phase `X a` without game oracles, classical post-processing `post a`. -/
theorem qWeight_twoPhase (pre : ProbComp γ) (X : γ → Closed W α) (post : γ → α → ProbComp β)
    (p : β → Prop) [DecidablePred p] (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1)
    (hX : ∀ a, RationalBorn (X a) ρ) :
    qWeight p (liftU pre >>= fun a ↦ X a >>= fun x ↦ liftU (post a x)) ρ =
      prob (pre >>= fun a ↦ toProbCompC (X a) ρ >>= post a) p := by
  have h1' : ENNReal.ofReal ρ.trace.re = 1 := by simp [h1]
  rw [← one_mul (prob _ _)]
  refine qWeight_liftU_bind _ _ _ _ _ _ fun a ↦ ?_
  rw [← h1']
  refine qWeight_bind_closed _ _ _ (fun x ρ' _ ↦ ?_) _ _ hρ (hX a)
  have := qWeight_liftU_bind p (post a x) (pure : β → Closed W β) pure
    (ENNReal.ofReal ρ'.trace.re) ρ' (fun x ↦ by simp)
  simpa using this

section smpre

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type}

/-- An SM-DT-PRE adversary with classical `choose` phase and quantum `invert` phase. -/
structure QSM_DT_PRE_Adversary (W : Type) [Fintype W]
    (P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) where
  /-- Classical state carried from `choose` to `invert`. -/
  State : Type
  /-- Classical target selection, as in `SM_DT_PRE_Adversary.choose`. -/
  choose : OracleComp
    (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  invert : State → PkSeed → Closed W (ℕ × M')
  /-- Initial workspace state of the second phase. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The classical adversary with the classical strategy of the quantum second phase. -/
noncomputable def QSM_DT_PRE_Adversary.toClassical {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_Adversary W P) : SM_DT_PRE_Adversary P where
  State := adv.State
  choose := adv.choose
  invert st pk := toProbCompC (adv.invert st pk) adv.ρ₀

/-- The SM-DT-PRE experiment (`SM_DT_PRE_Experiment`) with a quantum second phase. -/
noncomputable def qSM_DT_PRE_Experiment [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_Adversary W P) :
    Closed W Bool :=
  liftU (P.th.seedGen >>= fun pk ↦
      (simulateQ (SM_DT_PRE_oracles P pk) adv.choose).run ([], []) >>= fun r ↦
        pure (pk, r)) >>= fun a ↦
    adv.invert a.2.1 a.1 >>= fun jm ↦
      liftU (match a.2.2.1[jm.1]? with
        | none => pure false
        | some tx => pure (decide
            (P.th.eval a.1 tx.1 (P.emb jm.2) = P.th.eval a.1 tx.1 (P.emb tx.2))))

/-- Quantum SM-DT-PRE advantage. -/
noncomputable def qSM_DT_PRE_Advantage [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_PRE_Experiment adv) adv.ρ₀

/-- **Quantum SM-DT-PRE advantage = classical SM-DT-PRE advantage of the classical strategy.** -/
theorem qSM_DT_PRE_Advantage_eq [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_Adversary W P)
    (hQ : ∀ st pk, RationalBorn (adv.invert st pk) adv.ρ₀) :
    qSM_DT_PRE_Advantage adv = SM_DT_PRE_Advantage adv.toClassical := by
  rw [qSM_DT_PRE_Advantage, SM_DT_PRE_Advantage, ← prob_eq_evalDist_true, qSM_DT_PRE_Experiment,
    qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
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

/-- An SM-DT-UD adversary with classical `pick` phase and quantum `distinguish` phase. -/
structure QSM_DT_UD_Adversary (W : Type) [Fintype W]
    (P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) where
  /-- Classical state carried from `pick` to `distinguish`. -/
  State : Type
  /-- Classical target selection, as in `SM_DT_UD_Adversary.pick`. -/
  pick : OracleComp
    (unifSpec + (SM_DT_UD_challengeSpec Tweak Y + collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  distinguish : State → PkSeed → Closed W Bool
  /-- Initial workspace state of the second phase. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The classical adversary with the classical strategy of the quantum second phase. -/
noncomputable def QSM_DT_UD_Adversary.toClassical {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_Adversary W P) : SM_DT_UD_Adversary P where
  State := adv.State
  pick := adv.pick
  distinguish st pk := toProbCompC (adv.distinguish st pk) adv.ρ₀

/-- The SM-DT-UD experiment (`SM_DT_UD_Experiment`) in one world, with a quantum second phase. -/
noncomputable def qSM_DT_UD_Experiment [DecidableEq Tweak] (world : SM_DT_UD_World)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    Closed W Bool :=
  liftU (P.th.seedGen >>= fun pk ↦
      (simulateQ (SM_DT_UD_oracles world P pk) adv.pick).run ([], []) >>= fun r ↦
        pure (pk, r.1)) >>= fun a ↦
    adv.distinguish a.2 a.1 >>= fun b ↦ liftU (pure b)

/-- Quantum SM-DT-UD advantage: distance between the Born probabilities of output `true` in the
real and the ideal world. -/
noncomputable def qSM_DT_UD_Advantage [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) : ℝ≥0∞ :=
  ENNReal.absDiff (qWeight (· = true) (qSM_DT_UD_Experiment .real adv) adv.ρ₀)
    (qWeight (· = true) (qSM_DT_UD_Experiment .ideal adv) adv.ρ₀)

theorem qWeight_qSM_DT_UD_Experiment [DecidableEq Tweak] (world : SM_DT_UD_World)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P)
    (hQ : ∀ st pk, RationalBorn (adv.distinguish st pk) adv.ρ₀) :
    qWeight (· = true) (qSM_DT_UD_Experiment world adv) adv.ρ₀ =
      𝒟[SM_DT_UD_Experiment world adv.toClassical] {true} := by
  rw [← prob_eq_evalDist_true, qSM_DT_UD_Experiment,
    qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
  congr 1
  unfold SM_DT_UD_Experiment
  simp only [bind_assoc, pure_bind, bind_pure]
  rfl

/-- **Quantum SM-DT-UD advantage = classical SM-DT-UD advantage of the classical strategy.** -/
theorem qSM_DT_UD_Advantage_eq [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P)
    (hQ : ∀ st pk, RationalBorn (adv.distinguish st pk) adv.ρ₀) :
    qSM_DT_UD_Advantage adv = SM_DT_UD_Advantage adv.toClassical := by
  rw [qSM_DT_UD_Advantage, qWeight_qSM_DT_UD_Experiment .real adv hQ,
    qWeight_qSM_DT_UD_Experiment .ideal adv hQ]
  rfl

end smud

section tcrfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- A source-final-validity SM-DT-TCR adversary with classical `choose` phase and quantum `forge`
phase. -/
structure QTcrFV_Adversary (W : Type) [Fintype W]
    (P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y) where
  /-- Classical state carried from `choose` to `forge`. -/
  State : Type
  /-- Classical target selection. -/
  choose : OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
    SourceFinalValidity.collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  forge : State → PkSeed → Closed W (ℕ × M)
  /-- Initial workspace state of the second phase. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The classical adversary with the classical strategy of the quantum second phase. -/
noncomputable def QTcrFV_Adversary.toClassical
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) : SM_DT_TCR_SourceFinalValidity.Adversary P where
  State := adv.State
  choose := adv.choose
  forge st pk := toProbCompC (adv.forge st pk) adv.ρ₀

/-- `SM_DT_TCR_SourceFinalValidity.experiment` with a quantum second phase. -/
noncomputable def qTcrFV_Experiment [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) : Closed W Bool :=
  liftU (P.th.seedGen >>= fun pk ↦
      (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles P pk) adv.choose).run .initial >>=
        fun r ↦ pure (pk, r)) >>= fun a ↦
    adv.forge a.2.1 a.1 >>= fun jm ↦
      liftU (match a.2.2.challenges[jm.1]? with
        | none => pure false
        | some tm => pure (a.2.2.valid && decide
            (jm.2 ≠ tm.2 ∧ P.th.eval a.1 tm.1 jm.2 = P.th.eval a.1 tm.1 tm.2)))

/-- Quantum source-final-validity SM-DT-TCR advantage. -/
noncomputable def qTcrFV_Advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qTcrFV_Experiment adv) adv.ρ₀

/-- **Quantum = classical (of the classical strategy) for source-final-validity SM-DT-TCR.** -/
theorem qTcrFV_Advantage_eq [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) (hQ : ∀ st pk, RationalBorn (adv.forge st pk) adv.ρ₀) :
    qTcrFV_Advantage adv = SM_DT_TCR_SourceFinalValidity.advantage adv.toClassical := by
  rw [qTcrFV_Advantage, SM_DT_TCR_SourceFinalValidity.advantage, ← prob_eq_evalDist_true,
    qTcrFV_Experiment,
    qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
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

/-- A source-final-validity SM-DT-DSPR adversary with classical `choose` phase and quantum `guess`
phase. -/
structure QDsprFV_Adversary (W : Type) [Fintype W]
    (P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y) where
  /-- Classical state carried from `choose` to `guess`. -/
  State : Type
  /-- Classical target selection. -/
  choose : OracleComp (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tweak M Y +
    SourceFinalValidity.collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  guess : State → PkSeed → Closed W (ℕ × Bool)
  /-- Initial workspace state of the second phase. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The classical adversary with the classical strategy of the quantum second phase. -/
noncomputable def QDsprFV_Adversary.toClassical
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : SM_DT_DSPR_SourceFinalValidity.Adversary P where
  State := adv.State
  choose := adv.choose
  guess st pk := toProbCompC (adv.guess st pk) adv.ρ₀

/-- `SM_DT_DSPR_SourceFinalValidity.experiment` with a quantum second phase. -/
noncomputable def qDsprFV_Experiment [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : Closed W Bool :=
  liftU (P.th.seedGen >>= fun pk ↦
      (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles P pk) adv.choose).run .initial >>=
        fun r ↦ pure (pk, r)) >>= fun a ↦
    adv.guess a.2.1 a.1 >>= fun jb ↦
      liftU (match a.2.2.challenges[jb.1]? with
        | none => pure false
        | some tm => pure (a.2.2.valid && decide
            (TweakableHash.SecondPreimageExists P.th a.1 tm.1 tm.2 ↔
              jb.2 = true)))

/-- `SM_DT_DSPR_SourceFinalValidity.spExperiment` (the `SPprob` baseline) with a quantum second
phase. -/
noncomputable def qDsprFV_SpExperiment [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : Closed W Bool :=
  liftU (P.th.seedGen >>= fun pk ↦
      (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles P pk) adv.choose).run .initial >>=
        fun r ↦ pure (pk, r)) >>= fun a ↦
    adv.guess a.2.1 a.1 >>= fun jb ↦
      liftU (match a.2.2.challenges[jb.1]? with
        | none => pure false
        | some tm => pure (a.2.2.valid && decide
            (TweakableHash.SecondPreimageExists P.th a.1 tm.1 tm.2)))

/-- Quantum source-final-validity SM-DT-DSPR advantage: `Pr[DSPR] - Pr[SPprob]` with Born
probabilities. -/
noncomputable def qDsprFV_Advantage [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qDsprFV_Experiment adv) adv.ρ₀ -
    qWeight (· = true) (qDsprFV_SpExperiment adv) adv.ρ₀

/-- **Quantum = classical (of the classical strategy) for source-final-validity SM-DT-DSPR.** -/
theorem qDsprFV_Advantage_eq [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) (hQ : ∀ st pk, RationalBorn (adv.guess st pk) adv.ρ₀) :
    qDsprFV_Advantage adv = SM_DT_DSPR_SourceFinalValidity.advantage adv.toClassical := by
  have h1 : qWeight (· = true) (qDsprFV_Experiment adv) adv.ρ₀ =
      SM_DT_DSPR_SourceFinalValidity.Success adv.toClassical := by
    rw [SM_DT_DSPR_SourceFinalValidity.Success, ← prob_eq_evalDist_true, qDsprFV_Experiment,
      qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
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
  have h2 : qWeight (· = true) (qDsprFV_SpExperiment adv) adv.ρ₀ =
      SM_DT_DSPR_SourceFinalValidity.SPProbability adv.toClassical := by
    rw [SM_DT_DSPR_SourceFinalValidity.SPProbability, ← prob_eq_evalDist_true,
      qDsprFV_SpExperiment,
      qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
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
  rw [qDsprFV_Advantage, h1, h2]
  rfl

end dsprfv

/-! ## Named Born probabilities of the two-world games

The quantum advantages above are distances or differences of two Born probabilities.  The
individual probabilities are named here, with their classical counterparts, for statements in
linear form (`Pr[real] ≤ Pr[ideal] + …`). -/

section named

open TweakableHash

variable {K D R : Type}

/-- Born probability that the quantum distinguisher outputs `true` in the real PRF world. -/
noncomputable def qPrfRealPr (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) : ℝ≥0∞ :=
  qWeight (· = true) (qPrfRealExperiment prf Q) ρ

/-- Born probability that the quantum distinguisher outputs `true` in the ideal PRF world. -/
noncomputable def qPrfIdealPr [DecidableEq D] [SampleableType R]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) : ℝ≥0∞ :=
  qWeight (· = true) (qPrfIdealExperiment Q) ρ

lemma qPrfAdvantage_eq_absDiff [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) :
    qPrfAdvantage prf Q ρ = ENNReal.absDiff (qPrfRealPr prf Q ρ) (qPrfIdealPr Q ρ) := rfl

theorem qPrfRealPr_eq (prf : PRFScheme K D R) (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool)
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qPrfRealPr prf Q ρ = 𝒟[prf.prfRealExperiment (toProbComp Q ρ)] {true} :=
  qWeight_qPrfRealExperiment prf Q ρ hρ h1 hQ

theorem qPrfIdealPr_eq [DecidableEq D] [SampleableType R]
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qPrfIdealPr Q ρ = 𝒟[PRFScheme.prfIdealExperiment (toProbComp Q ρ)] {true} :=
  qWeight_qPrfIdealExperiment Q ρ hρ h1 hQ

variable {ι PkSeed Tweak M M' Y : Type}

/-- Born success probability in the real world of SM-DT-UD. -/
noncomputable def qSM_DT_UD_RealSuccess [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_UD_Experiment .real adv) adv.ρ₀

/-- Born success probability in the ideal world of SM-DT-UD. -/
noncomputable def qSM_DT_UD_IdealSuccess [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_UD_Experiment .ideal adv) adv.ρ₀

lemma qSM_DT_UD_Advantage_eq_absDiff [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_Advantage adv =
      ENNReal.absDiff (qSM_DT_UD_RealSuccess adv) (qSM_DT_UD_IdealSuccess adv) := rfl

theorem qSM_DT_UD_RealSuccess_eq [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P)
    (hQ : ∀ st pk, RationalBorn (adv.distinguish st pk) adv.ρ₀) :
    qSM_DT_UD_RealSuccess adv = SM_DT_UD_RealSuccess adv.toClassical :=
  qWeight_qSM_DT_UD_Experiment .real adv hQ

theorem qSM_DT_UD_IdealSuccess_eq [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P)
    (hQ : ∀ st pk, RationalBorn (adv.distinguish st pk) adv.ρ₀) :
    qSM_DT_UD_IdealSuccess adv = SM_DT_UD_IdealSuccess adv.toClassical :=
  qWeight_qSM_DT_UD_Experiment .ideal adv hQ

/-- Born probability of a correct prediction in source-final-validity SM-DT-DSPR. -/
noncomputable def qDsprFV_Success [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qDsprFV_Experiment adv) adv.ρ₀

/-- Born probability of the `SPprob` baseline of source-final-validity SM-DT-DSPR. -/
noncomputable def qDsprFV_SPProbability [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : ℝ≥0∞ :=
  qWeight (· = true) (qDsprFV_SpExperiment adv) adv.ρ₀

lemma qDsprFV_Advantage_eq_sub [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    qDsprFV_Advantage adv = qDsprFV_Success adv - qDsprFV_SPProbability adv := rfl

theorem qDsprFV_Success_eq [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) (hQ : ∀ st pk, RationalBorn (adv.guess st pk) adv.ρ₀) :
    qDsprFV_Success adv = SM_DT_DSPR_SourceFinalValidity.Success adv.toClassical := by
  rw [qDsprFV_Success, SM_DT_DSPR_SourceFinalValidity.Success, ← prob_eq_evalDist_true,
    qDsprFV_Experiment,
    qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
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

theorem qDsprFV_SPProbability_eq [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) (hQ : ∀ st pk, RationalBorn (adv.guess st pk) adv.ρ₀) :
    qDsprFV_SPProbability adv =
      SM_DT_DSPR_SourceFinalValidity.SPProbability adv.toClassical := by
  rw [qDsprFV_SPProbability, SM_DT_DSPR_SourceFinalValidity.SPProbability,
    ← prob_eq_evalDist_true, qDsprFV_SpExperiment,
    qWeight_twoPhase _ _ _ _ _ adv.posSemidef adv.trace_eq_one fun a ↦ hQ _ _]
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

end named

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_game
open PQ.Interactive in
#print axioms qPrfAdvantage_eq
open PQ.Interactive in
#print axioms qItsrAdvantage_eq
open PQ.Interactive in
#print axioms qSM_DT_TCR_Advantage_eq
open PQ.Interactive in
#print axioms qSM_DT_PRE_Advantage_eq
open PQ.Interactive in
#print axioms qSM_DT_UD_Advantage_eq
open PQ.Interactive in
#print axioms qTcrFV_Advantage_eq
open PQ.Interactive in
#print axioms qDsprFV_Advantage_eq
