import PQ.Interactive.Games

/-!
# General quantum two-phase games

The two-phase games of `Games.lean` (`QSM_DT_TCR_Adversary`, …) restrict the adversary to a
classical first phase and a quantum second phase started from a fresh state.  Here are the
GENERAL quantum versions of SM-DT-TCR, SM-DT-PRE, SM-DT-UD and the source-final-validity
SM-DT-TCR / SM-DT-DSPR games: BOTH phases are quantum machines on the same workspace `W`,

* `choose : QOC W (unifSpec + (challengeSpec + collectionSpec)) State` — a quantum machine with
  classical access to the challenge and collection oracles of the game, seed hidden;
* `forge : State → PkSeed → Closed W _` — a quantum machine without oracle, given the seed and
  the classical state;

and the workspace state is carried across the seed reveal: the experiment is VCVio's experiment
with the machines in place, as ONE closed machine
`liftU seedGen >>= fun pk ↦ close (oracles pk) choose init >>= fun r ↦ forge r.1 pk >>= …`,
and `qWeight` threads the (unnormalised) workspace state through `>>=`.  Advantages are Born
probabilities.  These games give the adversary a quantum workspace but only CLASSICAL access to
the game's oracles and no quantum access to the hash function.  Consequently they are not new
assumptions: by `q…AdvantageG_le_of_forall` (`PQ/Interactive/ApproxGeneral.lean`) every advantage
in a general quantum game is a limit of advantages of (computationally unbounded) classical
adversaries, i.e. in the standard model these games are equivalent to the classical games against
unbounded adversaries.  Quantum access to the hash is modelled separately (`PQ/QROM`,
`PQ/Interactive/QromBridge*.lean`).

For each game:

* `…AdversaryG`, `…ExperimentG`, `…AdvantageG`: the general game;
* `…Adversary.toGeneral` and `…Advantage_toGeneral`: the restricted adversaries of `Games.lean`
  are general adversaries with the same advantage (classical first phase lifted by `liftQ`);
* `…Adversary.toQuantum` / `…AdvantageG_ofClassical`: a classical VCVio adversary, lifted, has
  exactly its VCVio advantage in the general quantum game (the classical game is the special
  case).

The limit theorems for general adversaries (`q…AdvantageG_le_of_forall`: a bound valid for all
classical adversaries holds for all general quantum adversaries) are in
`PQ/Interactive/ApproxGeneral.lean`, not in this file.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}

/-- Closing a classical program (lifted into quantum machines) is running the implementation on
it. -/
theorem close_liftQ {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (ob : OracleComp spec α) (s : σ) :
    close (W := W) impl (liftQ ob) s = liftU ((simulateQ impl ob).run s) := by
  induction ob using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftQ_query_bind, close_query_bind, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
      liftU_bind]
    simp only [ih]

/-! ## SM-DT-TCR -/

section smtcr

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- A general quantum SM-DT-TCR adversary: both phases are quantum machines on the workspace
`W`; the workspace state persists across the seed reveal; `State` is the classical state passed
between the phases. -/
structure QSM_DT_TCR_AdversaryG (W : Type) [Fintype W]
    (P : SM_DT_TCR_Problem ι PkSeed Tweak M Y) where
  /-- Classical state carried from `choose` to `forge` (besides the workspace). -/
  State : Type
  /-- Quantum target selection with classical access to the challenge and collection oracles. -/
  choose : QOC W
    (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec P.thColl)) State
  /-- Quantum second phase, given the seed. -/
  forge : State → PkSeed → Closed W (ℕ × M)
  /-- Initial workspace state. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The SM-DT-TCR experiment (`SM_DT_TCR_Experiment`) with quantum machines in both phases. -/
noncomputable def qSM_DT_TCR_ExperimentG [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_AdversaryG W P) :
    Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    close (SM_DT_TCR_oracles P pk) adv.choose ([], []) >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2))

/-- Advantage in the general quantum SM-DT-TCR game. -/
noncomputable def qSM_DT_TCR_AdvantageG [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_TCR_ExperimentG adv) adv.ρ₀

/-- A restricted adversary (classical first phase) as a general one. -/
def QSM_DT_TCR_Adversary.toGeneral {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_Adversary W P) : QSM_DT_TCR_AdversaryG W P where
  State := adv.State
  choose := liftQ adv.choose
  forge := adv.forge
  ρ₀ := adv.ρ₀
  posSemidef := adv.posSemidef
  trace_eq_one := adv.trace_eq_one

theorem qSM_DT_TCR_ExperimentG_toGeneral [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P) :
    qSM_DT_TCR_ExperimentG adv.toGeneral = qSM_DT_TCR_Experiment adv := by
  unfold qSM_DT_TCR_ExperimentG qSM_DT_TCR_Experiment
  simp only [QSM_DT_TCR_Adversary.toGeneral, close_liftQ]
  rfl

/-- **The restricted game is the general game at restricted adversaries.** -/
theorem qSM_DT_TCR_Advantage_toGeneral [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P) :
    qSM_DT_TCR_Advantage adv = qSM_DT_TCR_AdvantageG adv.toGeneral := by
  rw [qSM_DT_TCR_AdvantageG, qSM_DT_TCR_ExperimentG_toGeneral]
  rfl

/-- A classical adversary as a quantum adversary (its code never touches the workspace). -/
def QSM_DT_TCR_Adversary.ofClassical {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (A : SM_DT_TCR_Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) :
    QSM_DT_TCR_Adversary W P where
  State := A.State
  choose := A.choose
  forge st pk := liftU (A.forge st pk)
  ρ₀ := ρ₀
  posSemidef := h₁
  trace_eq_one := h₂

/-- **The classical game is the special case**: a classical adversary, lifted, has its VCVio
advantage in the general quantum game. -/
theorem qSM_DT_TCR_AdvantageG_ofClassical [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (A : SM_DT_TCR_Adversary P) (ρ₀ : Matrix W W ℂ)
    (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) :
    qSM_DT_TCR_AdvantageG (QSM_DT_TCR_Adversary.ofClassical A ρ₀ h₁ h₂).toGeneral =
      SM_DT_TCR_Advantage A := by
  rw [← qSM_DT_TCR_Advantage_toGeneral,
    qSM_DT_TCR_Advantage_eq _ fun st pk ↦ rationalBorn_liftQ (spec := unifSpec) _ _]
  congr 1
  obtain ⟨S, c, f⟩ := A
  simp [QSM_DT_TCR_Adversary.ofClassical, QSM_DT_TCR_Adversary.toClassical]

end smtcr

/-! ## SM-DT-PRE -/

section smpre

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type}

/-- A general quantum SM-DT-PRE adversary (both phases quantum, workspace carried across). -/
structure QSM_DT_PRE_AdversaryG (W : Type) [Fintype W]
    (P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) where
  /-- Classical state carried from `choose` to `invert`. -/
  State : Type
  /-- Quantum target selection. -/
  choose : QOC W
    (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  invert : State → PkSeed → Closed W (ℕ × M')
  /-- Initial workspace state. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The SM-DT-PRE experiment with quantum machines in both phases. -/
noncomputable def qSM_DT_PRE_ExperimentG [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_AdversaryG W P) :
    Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    close (SM_DT_PRE_oracles P pk) adv.choose ([], []) >>= fun r ↦
      adv.invert r.1 pk >>= fun jm ↦
        liftU (match r.2.1[jm.1]? with
          | none => pure false
          | some tx => pure (decide
              (P.th.eval pk tx.1 (P.emb jm.2) = P.th.eval pk tx.1 (P.emb tx.2))))

/-- Advantage in the general quantum SM-DT-PRE game. -/
noncomputable def qSM_DT_PRE_AdvantageG [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_PRE_ExperimentG adv) adv.ρ₀

/-- A restricted adversary as a general one. -/
def QSM_DT_PRE_Adversary.toGeneral {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_PRE_Adversary W P) : QSM_DT_PRE_AdversaryG W P where
  State := adv.State
  choose := liftQ adv.choose
  invert := adv.invert
  ρ₀ := adv.ρ₀
  posSemidef := adv.posSemidef
  trace_eq_one := adv.trace_eq_one

theorem qSM_DT_PRE_ExperimentG_toGeneral [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_Adversary W P) :
    qSM_DT_PRE_ExperimentG adv.toGeneral = qSM_DT_PRE_Experiment adv := by
  unfold qSM_DT_PRE_ExperimentG qSM_DT_PRE_Experiment
  simp only [QSM_DT_PRE_Adversary.toGeneral, close_liftQ, liftU_bind, liftU_pure, bind_assoc,
    pure_bind]
  rfl

theorem qSM_DT_PRE_Advantage_toGeneral [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_PRE_Adversary W P) :
    qSM_DT_PRE_Advantage adv = qSM_DT_PRE_AdvantageG adv.toGeneral := by
  rw [qSM_DT_PRE_AdvantageG, qSM_DT_PRE_ExperimentG_toGeneral]
  rfl

/-- A classical adversary as a quantum adversary. -/
def QSM_DT_PRE_Adversary.ofClassical {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
    (A : SM_DT_PRE_Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) :
    QSM_DT_PRE_Adversary W P where
  State := A.State
  choose := A.choose
  invert st pk := liftU (A.invert st pk)
  ρ₀ := ρ₀
  posSemidef := h₁
  trace_eq_one := h₂

theorem qSM_DT_PRE_AdvantageG_ofClassical [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {P : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (A : SM_DT_PRE_Adversary P) (ρ₀ : Matrix W W ℂ)
    (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) :
    qSM_DT_PRE_AdvantageG (QSM_DT_PRE_Adversary.ofClassical A ρ₀ h₁ h₂).toGeneral =
      SM_DT_PRE_Advantage A := by
  rw [← qSM_DT_PRE_Advantage_toGeneral,
    qSM_DT_PRE_Advantage_eq _ fun st pk ↦ rationalBorn_liftQ (spec := unifSpec) _ _]
  congr 1
  obtain ⟨S, c, f⟩ := A
  simp [QSM_DT_PRE_Adversary.ofClassical, QSM_DT_PRE_Adversary.toClassical]

end smpre

/-! ## SM-DT-UD -/

section smud

open TweakableHash

variable {ι PkSeed Tweak M M' Y : Type}

/-- A general quantum SM-DT-UD adversary (both phases quantum, workspace carried across). -/
structure QSM_DT_UD_AdversaryG (W : Type) [Fintype W]
    (P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) where
  /-- Classical state carried from `pick` to `distinguish`. -/
  State : Type
  /-- Quantum target selection. -/
  pick : QOC W
    (unifSpec + (SM_DT_UD_challengeSpec Tweak Y + collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  distinguish : State → PkSeed → Closed W Bool
  /-- Initial workspace state. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- The SM-DT-UD experiment in one world with quantum machines in both phases. -/
noncomputable def qSM_DT_UD_ExperimentG [DecidableEq Tweak] (world : SM_DT_UD_World)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) :
    Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    close (SM_DT_UD_oracles world P pk) adv.pick ([], []) >>= fun r ↦
      adv.distinguish r.1 pk

/-- Born success probability in the real world of the general quantum SM-DT-UD game. -/
noncomputable def qSM_DT_UD_RealSuccessG [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_UD_ExperimentG .real adv) adv.ρ₀

/-- Born success probability in the ideal world of the general quantum SM-DT-UD game. -/
noncomputable def qSM_DT_UD_IdealSuccessG [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qSM_DT_UD_ExperimentG .ideal adv) adv.ρ₀

/-- Advantage in the general quantum SM-DT-UD game. -/
noncomputable def qSM_DT_UD_AdvantageG [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_AdversaryG W P) : ℝ≥0∞ :=
  ENNReal.absDiff (qSM_DT_UD_RealSuccessG adv) (qSM_DT_UD_IdealSuccessG adv)

/-- A restricted adversary as a general one. -/
def QSM_DT_UD_Adversary.toGeneral {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (adv : QSM_DT_UD_Adversary W P) : QSM_DT_UD_AdversaryG W P where
  State := adv.State
  pick := liftQ adv.pick
  distinguish := adv.distinguish
  ρ₀ := adv.ρ₀
  posSemidef := adv.posSemidef
  trace_eq_one := adv.trace_eq_one

theorem qSM_DT_UD_ExperimentG_toGeneral [DecidableEq Tweak] (world : SM_DT_UD_World)
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_ExperimentG world adv.toGeneral = qSM_DT_UD_Experiment world adv := by
  unfold qSM_DT_UD_ExperimentG qSM_DT_UD_Experiment
  simp only [QSM_DT_UD_Adversary.toGeneral, close_liftQ, liftU_bind, liftU_pure, bind_assoc,
    pure_bind, bind_pure]

theorem qSM_DT_UD_RealSuccess_toGeneral [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_RealSuccess adv = qSM_DT_UD_RealSuccessG adv.toGeneral := by
  rw [qSM_DT_UD_RealSuccessG, qSM_DT_UD_ExperimentG_toGeneral]
  rfl

theorem qSM_DT_UD_IdealSuccess_toGeneral [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_IdealSuccess adv = qSM_DT_UD_IdealSuccessG adv.toGeneral := by
  rw [qSM_DT_UD_IdealSuccessG, qSM_DT_UD_ExperimentG_toGeneral]
  rfl

theorem qSM_DT_UD_Advantage_toGeneral [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : QSM_DT_UD_Adversary W P) :
    qSM_DT_UD_Advantage adv = qSM_DT_UD_AdvantageG adv.toGeneral := by
  rw [qSM_DT_UD_AdvantageG, ← qSM_DT_UD_RealSuccess_toGeneral,
    ← qSM_DT_UD_IdealSuccess_toGeneral]
  rfl

/-- A classical adversary as a quantum adversary. -/
def QSM_DT_UD_Adversary.ofClassical {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y}
    (A : SM_DT_UD_Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) :
    QSM_DT_UD_Adversary W P where
  State := A.State
  pick := A.pick
  distinguish st pk := liftU (A.distinguish st pk)
  ρ₀ := ρ₀
  posSemidef := h₁
  trace_eq_one := h₂

theorem qSM_DT_UD_AdvantageG_ofClassical [DecidableEq Tweak]
    {P : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (A : SM_DT_UD_Adversary P) (ρ₀ : Matrix W W ℂ)
    (h₁ : ρ₀.PosSemidef) (h₂ : ρ₀.trace = 1) :
    qSM_DT_UD_AdvantageG (QSM_DT_UD_Adversary.ofClassical A ρ₀ h₁ h₂).toGeneral =
      SM_DT_UD_Advantage A := by
  rw [← qSM_DT_UD_Advantage_toGeneral,
    qSM_DT_UD_Advantage_eq _ fun st pk ↦ rationalBorn_liftQ (spec := unifSpec) _ _]
  congr 1
  obtain ⟨S, c, f⟩ := A
  simp [QSM_DT_UD_Adversary.ofClassical, QSM_DT_UD_Adversary.toClassical]

end smud

/-! ## Source-final-validity SM-DT-TCR -/

section tcrfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- A general quantum source-final-validity SM-DT-TCR adversary. -/
structure QTcrFV_AdversaryG (W : Type) [Fintype W]
    (P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y) where
  /-- Classical state carried from `choose` to `forge`. -/
  State : Type
  /-- Quantum target selection. -/
  choose : QOC W (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
    SourceFinalValidity.collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  forge : State → PkSeed → Closed W (ℕ × M)
  /-- Initial workspace state. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- `SM_DT_TCR_SourceFinalValidity.experiment` with quantum machines in both phases. -/
noncomputable def qTcrFV_ExperimentG [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_AdversaryG W P) : Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    close (SM_DT_TCR_SourceFinalValidity.oracles P pk) adv.choose .initial >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦
        liftU (match r.2.challenges[jm.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide
              (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2)))

/-- Advantage in the general quantum source-final-validity SM-DT-TCR game. -/
noncomputable def qTcrFV_AdvantageG [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qTcrFV_ExperimentG adv) adv.ρ₀

/-- A restricted adversary as a general one. -/
def QTcrFV_Adversary.toGeneral {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QTcrFV_Adversary W P) : QTcrFV_AdversaryG W P where
  State := adv.State
  choose := liftQ adv.choose
  forge := adv.forge
  ρ₀ := adv.ρ₀
  posSemidef := adv.posSemidef
  trace_eq_one := adv.trace_eq_one

theorem qTcrFV_ExperimentG_toGeneral [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y} (adv : QTcrFV_Adversary W P) :
    qTcrFV_ExperimentG adv.toGeneral = qTcrFV_Experiment adv := by
  unfold qTcrFV_ExperimentG qTcrFV_Experiment
  simp only [QTcrFV_Adversary.toGeneral, close_liftQ, liftU_bind, liftU_pure, bind_assoc,
    pure_bind]
  rfl

theorem qTcrFV_Advantage_toGeneral [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y} (adv : QTcrFV_Adversary W P) :
    qTcrFV_Advantage adv = qTcrFV_AdvantageG adv.toGeneral := by
  rw [qTcrFV_AdvantageG, qTcrFV_ExperimentG_toGeneral]
  rfl

/-- A classical adversary as a quantum adversary. -/
def QTcrFV_Adversary.ofClassical {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (A : SM_DT_TCR_SourceFinalValidity.Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) : QTcrFV_Adversary W P where
  State := A.State
  choose := A.choose
  forge st pk := liftU (A.forge st pk)
  ρ₀ := ρ₀
  posSemidef := h₁
  trace_eq_one := h₂

theorem qTcrFV_AdvantageG_ofClassical [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (A : SM_DT_TCR_SourceFinalValidity.Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) :
    qTcrFV_AdvantageG (QTcrFV_Adversary.ofClassical A ρ₀ h₁ h₂).toGeneral =
      SM_DT_TCR_SourceFinalValidity.advantage A := by
  rw [← qTcrFV_Advantage_toGeneral,
    qTcrFV_Advantage_eq _ fun st pk ↦ rationalBorn_liftQ (spec := unifSpec) _ _]
  congr 1
  obtain ⟨S, c, f⟩ := A
  simp [QTcrFV_Adversary.ofClassical, QTcrFV_Adversary.toClassical]

end tcrfv

/-! ## Source-final-validity SM-DT-DSPR -/

section dsprfv

open TweakableHash

variable {ι PkSeed Tweak M Y : Type}

/-- A general quantum source-final-validity SM-DT-DSPR adversary. -/
structure QDsprFV_AdversaryG (W : Type) [Fintype W]
    (P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y) where
  /-- Classical state carried from `choose` to `guess`. -/
  State : Type
  /-- Quantum target selection. -/
  choose : QOC W (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tweak M Y +
    SourceFinalValidity.collectionSpec P.thColl)) State
  /-- Quantum second phase. -/
  guess : State → PkSeed → Closed W (ℕ × Bool)
  /-- Initial workspace state. -/
  ρ₀ : Matrix W W ℂ
  posSemidef : ρ₀.PosSemidef
  trace_eq_one : ρ₀.trace = 1

/-- `SM_DT_DSPR_SourceFinalValidity.experiment` with quantum machines in both phases. -/
noncomputable def qDsprFV_ExperimentG [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) : Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    close (SM_DT_DSPR_SourceFinalValidity.oracles P pk) adv.choose .initial >>= fun r ↦
      adv.guess r.1 pk >>= fun jb ↦
        liftU (match r.2.challenges[jb.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide
              (TweakableHash.SecondPreimageExists P.th pk tm.1 tm.2 ↔ jb.2 = true)))

/-- `SM_DT_DSPR_SourceFinalValidity.spExperiment` with quantum machines in both phases. -/
noncomputable def qDsprFV_SpExperimentG [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) : Closed W Bool :=
  liftU P.th.seedGen >>= fun pk ↦
    close (SM_DT_DSPR_SourceFinalValidity.oracles P pk) adv.choose .initial >>= fun r ↦
      adv.guess r.1 pk >>= fun jb ↦
        liftU (match r.2.challenges[jb.1]? with
          | none => pure false
          | some tm => pure (r.2.valid && decide
              (TweakableHash.SecondPreimageExists P.th pk tm.1 tm.2)))

/-- Born probability of a correct prediction in the general quantum DSPR game. -/
noncomputable def qDsprFV_SuccessG [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qDsprFV_ExperimentG adv) adv.ρ₀

/-- Born probability of the `SPprob` baseline in the general quantum DSPR game. -/
noncomputable def qDsprFV_SPProbabilityG [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) : ℝ≥0∞ :=
  qWeight (· = true) (qDsprFV_SpExperimentG adv) adv.ρ₀

/-- Advantage in the general quantum source-final-validity SM-DT-DSPR game. -/
noncomputable def qDsprFV_AdvantageG [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_AdversaryG W P) : ℝ≥0∞ :=
  qDsprFV_SuccessG adv - qDsprFV_SPProbabilityG adv

/-- A restricted adversary as a general one. -/
def QDsprFV_Adversary.toGeneral {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : QDsprFV_AdversaryG W P where
  State := adv.State
  choose := liftQ adv.choose
  guess := adv.guess
  ρ₀ := adv.ρ₀
  posSemidef := adv.posSemidef
  trace_eq_one := adv.trace_eq_one

theorem qDsprFV_ExperimentG_toGeneral [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    qDsprFV_ExperimentG adv.toGeneral = qDsprFV_Experiment adv := by
  unfold qDsprFV_ExperimentG qDsprFV_Experiment
  simp only [QDsprFV_Adversary.toGeneral, close_liftQ, liftU_bind, liftU_pure, bind_assoc,
    pure_bind]
  rfl

theorem qDsprFV_SpExperimentG_toGeneral [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    qDsprFV_SpExperimentG adv.toGeneral = qDsprFV_SpExperiment adv := by
  unfold qDsprFV_SpExperimentG qDsprFV_SpExperiment
  simp only [QDsprFV_Adversary.toGeneral, close_liftQ, liftU_bind, liftU_pure, bind_assoc,
    pure_bind]
  rfl

theorem qDsprFV_Success_toGeneral [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : qDsprFV_Success adv = qDsprFV_SuccessG adv.toGeneral := by
  rw [qDsprFV_SuccessG, qDsprFV_ExperimentG_toGeneral]
  rfl

theorem qDsprFV_SPProbability_toGeneral [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) :
    qDsprFV_SPProbability adv = qDsprFV_SPProbabilityG adv.toGeneral := by
  rw [qDsprFV_SPProbabilityG, qDsprFV_SpExperimentG_toGeneral]
  rfl

theorem qDsprFV_Advantage_toGeneral [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (adv : QDsprFV_Adversary W P) : qDsprFV_Advantage adv = qDsprFV_AdvantageG adv.toGeneral := by
  rw [qDsprFV_AdvantageG, ← qDsprFV_Success_toGeneral, ← qDsprFV_SPProbability_toGeneral]
  rfl

/-- A classical adversary as a quantum adversary. -/
def QDsprFV_Adversary.ofClassical {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (A : SM_DT_DSPR_SourceFinalValidity.Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) : QDsprFV_Adversary W P where
  State := A.State
  choose := A.choose
  guess st pk := liftU (A.guess st pk)
  ρ₀ := ρ₀
  posSemidef := h₁
  trace_eq_one := h₂

theorem qDsprFV_AdvantageG_ofClassical [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {P : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (A : SM_DT_DSPR_SourceFinalValidity.Adversary P) (ρ₀ : Matrix W W ℂ) (h₁ : ρ₀.PosSemidef)
    (h₂ : ρ₀.trace = 1) :
    qDsprFV_AdvantageG (QDsprFV_Adversary.ofClassical A ρ₀ h₁ h₂).toGeneral =
      SM_DT_DSPR_SourceFinalValidity.advantage A := by
  rw [← qDsprFV_Advantage_toGeneral,
    qDsprFV_Advantage_eq _ fun st pk ↦ rationalBorn_liftQ (spec := unifSpec) _ _]
  congr 1
  obtain ⟨S, c, f⟩ := A
  simp [QDsprFV_Adversary.ofClassical, QDsprFV_Adversary.toClassical]

end dsprfv

end PQ.Interactive

open PQ.Interactive in
#print axioms close_liftQ
open PQ.Interactive in
#print axioms qSM_DT_TCR_Advantage_toGeneral
open PQ.Interactive in
#print axioms qSM_DT_TCR_AdvantageG_ofClassical
open PQ.Interactive in
#print axioms qSM_DT_PRE_AdvantageG_ofClassical
open PQ.Interactive in
#print axioms qSM_DT_UD_AdvantageG_ofClassical
open PQ.Interactive in
#print axioms qTcrFV_AdvantageG_ofClassical
open PQ.Interactive in
#print axioms qDsprFV_AdvantageG_ofClassical
