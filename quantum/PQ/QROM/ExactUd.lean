import PQ.QROM.ExactPre
import PQ.QROM.ExactFv

/-!
# Distinguishing-type exact games in the QROM: seed hiding

For the two distinguishing-type games of the reduction, VCVio's `SM_DT_UD_Experiment`
(`…/TweakableHash/SMDTUD.lean`) and `SM_DT_DSPR_SourceFinalValidity` (`…/SMDTDSPRFinalValidity.lean`),
this file defines the exact two-phase experiments in the QROM (model: `PQ/QROM/TwoPhaseGame.lean`)
and proves the seed-hiding step: each experiment is within `4 q₁ / √|Sd|` of the corresponding
*hybrid* experiment, in which phase 1 has quantum access to a function independent of the row of
the hash at the seed.  The remaining step (the distinguishing bound in the hybrid world, where
phase 2 is a `q₂`-query algorithm against a row that is fresh except for the classical answers)
is not proved here; the theorems below take the hybrid-world advantage as it is.

## SM-DT-UD

The classical oracles are those of the PRE game (`preChT`, `PreState`): challenge requests
`Sum.inl t` (rejected on cap / reused tweak / collection clash) and collection requests
`Sum.inr (t, m)`.  Real world (`udReal`): the accepted challenge `t` is answered
`Th (P, (t, xs t))` for planted uniform `xs : Tw → Msg` (`M' = M`, `emb = id`, uniform inputs).
Ideal world (`udIdeal`): it is answered `ys t` for uniform `ys : Tw → Y` (uniform outputs).
Phase 2 returns a bit; the experiment outputs it (`udWin`).

## SM-DT-DSPR, source final validity

The classical oracles and the validity predicate are those of `PQ/QROM/ExactFv.lean`
(`fvCh`, `FvValid`).  Phase 2 returns `(j, b)`.  `dsprSucc`: valid, the `j`-th target `(t, m)`
exists and `b` is the truth value of "`m` has a second preimage under `Th (P, (t, ·))`".
`dsprSP`: valid, the `j`-th target exists and has a second preimage (VCVio's `spExperiment`).
The advantage is the truncated difference `dsprSucc - dsprSP`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type}

theorem avg_add_const_le {T : Type} [Fintype T] (f : T → ℝ≥0∞) (c : ℝ≥0∞) :
    avg (fun t ↦ f t + c) ≤ avg f + c := by
  have h : avg (fun t ↦ f t + c) = avg f + avg fun _ : T ↦ c := by
    unfold avg
    simp only [mul_add, Finset.sum_add_distrib]
  rw [h]
  exact add_le_add le_rfl (avg_le fun _ ↦ le_rfl)

section Exp

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}

/-- The seed-hiding loss, additive form: `4 q₁ / √|Sd|`. -/
noncomputable def seedLoss (Sd : Type) [Fintype Sd] (q₁ : ℕ) : ℝ≥0∞ :=
  2 * (2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ))

/-! ## SM-DT-UD -/

section UD

variable (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
  (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A)
  (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Bool) u)

/-- The UD experiment outputs the bit of phase 2. -/
def udWin (_ : Tw × Msg → Y) (b : Bool) (_ : PreState Tw Msg) : Prop := b = true

/-- **SM-DT-UD, real world**: challenges are hash images of planted uniform messages. -/
noncomputable def udReal : ℝ≥0∞ :=
  avg fun xs : Tw → Msg ↦ twoPhaseExp I ρ (preCh cap xs) preInit n x ph2 udWin

/-- **SM-DT-UD, ideal world**: challenges are uniform outputs. -/
noncomputable def udIdeal : ℝ≥0∞ :=
  avg fun ys : Tw → Y ↦ twoPhaseExp I ρ (fun a ↦ preChT cap ys a) preInit n x ph2 udWin

/-- The real world with phase 1 decoupled from the row of the seed. -/
noncomputable def udRealHyb : ℝ≥0∞ :=
  avg fun xs : Tw → Msg ↦ twoPhaseHyb I ρ (preCh cap xs) preInit n x ph2 udWin

/-- The ideal world with phase 1 decoupled from the row of the seed. -/
noncomputable def udIdealHyb : ℝ≥0∞ :=
  avg fun ys : Tw → Y ↦ twoPhaseHyb I ρ (fun a ↦ preChT cap ys a) preInit n x ph2 udWin

variable {I ρ cap n x ph2} {q₁ q₂ : ℕ}

theorem udReal_le_hyb_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udReal I ρ cap n x ph2 ≤ udRealHyb I ρ cap n x ph2 + seedLoss Sd q₁ :=
  (avg_mono fun _ ↦ twoPhaseExp_le_hyb_add hx h2).trans (avg_add_const_le _ _)

theorem udRealHyb_le_real_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udRealHyb I ρ cap n x ph2 ≤ udReal I ρ cap n x ph2 + seedLoss Sd q₁ :=
  (avg_mono fun _ ↦ twoPhaseHyb_le_exp_add hx h2).trans (avg_add_const_le _ _)

theorem udIdeal_le_hyb_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udIdeal I ρ cap n x ph2 ≤ udIdealHyb I ρ cap n x ph2 + seedLoss Sd q₁ :=
  (avg_mono fun _ ↦ twoPhaseExp_le_hyb_add hx h2).trans (avg_add_const_le _ _)

theorem udIdealHyb_le_ideal_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udIdealHyb I ρ cap n x ph2 ≤ udIdeal I ρ cap n x ph2 + seedLoss Sd q₁ :=
  (avg_mono fun _ ↦ twoPhaseHyb_le_exp_add hx h2).trans (avg_add_const_le _ _)

/-- **SM-DT-UD, seed hiding**: if the hybrid worlds are `δ`-close, the real and ideal worlds are
`δ + 8 q₁ / √|Sd|`-close (one direction). -/
theorem udExact_real_le_ideal_add_of_hyb {δ : ℝ≥0∞} (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hhyb : udRealHyb I ρ cap n x ph2 ≤ udIdealHyb I ρ cap n x ph2 + δ) :
    udReal I ρ cap n x ph2 ≤ udIdeal I ρ cap n x ph2 + (δ + 2 * seedLoss Sd q₁) :=
  calc udReal I ρ cap n x ph2 ≤ udRealHyb I ρ cap n x ph2 + seedLoss Sd q₁ :=
        udReal_le_hyb_add hx h2
    _ ≤ (udIdealHyb I ρ cap n x ph2 + δ) + seedLoss Sd q₁ := add_le_add hhyb le_rfl
    _ ≤ ((udIdeal I ρ cap n x ph2 + seedLoss Sd q₁) + δ) + seedLoss Sd q₁ :=
        add_le_add (add_le_add (udIdealHyb_le_ideal_add hx h2) le_rfl) le_rfl
    _ = udIdeal I ρ cap n x ph2 + (δ + 2 * seedLoss Sd q₁) := by ring

/-- **SM-DT-UD, seed hiding**, other direction. -/
theorem udExact_ideal_le_real_add_of_hyb {δ : ℝ≥0∞} (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hhyb : udIdealHyb I ρ cap n x ph2 ≤ udRealHyb I ρ cap n x ph2 + δ) :
    udIdeal I ρ cap n x ph2 ≤ udReal I ρ cap n x ph2 + (δ + 2 * seedLoss Sd q₁) :=
  calc udIdeal I ρ cap n x ph2 ≤ udIdealHyb I ρ cap n x ph2 + seedLoss Sd q₁ :=
        udIdeal_le_hyb_add hx h2
    _ ≤ (udRealHyb I ρ cap n x ph2 + δ) + seedLoss Sd q₁ := add_le_add hhyb le_rfl
    _ ≤ ((udReal I ρ cap n x ph2 + seedLoss Sd q₁) + δ) + seedLoss Sd q₁ :=
        add_le_add (add_le_add (udRealHyb_le_real_add hx h2) le_rfl) le_rfl
    _ = udReal I ρ cap n x ph2 + (δ + 2 * seedLoss Sd q₁) := by ring

end UD

/-! ## SM-DT-DSPR, source final validity -/

section DSPR

/-- `m` has a distinct second preimage under the row `a` at the tweak `t`. -/
def HasSecondPreimage (a : Tw × Msg → Y) (t : Tw) (m : Msg) : Prop :=
  ∃ m' : Msg, m ≠ m' ∧ a (t, m) = a (t, m')

/-- DSPR success: valid, the `j`-th target exists and the bit predicts whether it has a second
preimage. -/
def dsprWin (cap : ℕ) (a : Tw × Msg → Y) (r : ℕ × Bool) (s : FvState Tw Msg) : Prop :=
  FvValid cap s ∧ ∃ t m, s.chal[r.1]? = some (t, m) ∧ (HasSecondPreimage a t m ↔ r.2 = true)

/-- The `SPprob` baseline: valid, the `j`-th target exists and has a second preimage. -/
def dsprSPWin (cap : ℕ) (a : Tw × Msg → Y) (r : ℕ × Bool) (s : FvState Tw Msg) : Prop :=
  FvValid cap s ∧ ∃ t m, s.chal[r.1]? = some (t, m) ∧ HasSecondPreimage a t m

variable (I : L.Interp) (ρ : SubState A) (cap n : ℕ)
  (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A)
  (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Bool) u)

/-- **SM-DT-DSPR success probability** (source final validity) in the QROM. -/
noncomputable def dsprSucc : ℝ≥0∞ := twoPhaseExp I ρ fvCh fvInit n x ph2 (dsprWin cap)

/-- **The `SPprob` baseline** of the same adversary. -/
noncomputable def dsprSP : ℝ≥0∞ := twoPhaseExp I ρ fvCh fvInit n x ph2 (dsprSPWin cap)

/-- Success with phase 1 decoupled from the row of the seed. -/
noncomputable def dsprSuccHyb : ℝ≥0∞ := twoPhaseHyb I ρ fvCh fvInit n x ph2 (dsprWin cap)

/-- Baseline with phase 1 decoupled from the row of the seed. -/
noncomputable def dsprSPHyb : ℝ≥0∞ := twoPhaseHyb I ρ fvCh fvInit n x ph2 (dsprSPWin cap)

variable {I ρ cap n x ph2} {q₁ q₂ : ℕ}

/-- **SM-DT-DSPR, seed hiding**: the advantage `Success - SPprob` is at most the advantage in
the hybrid world plus `8 q₁ / √|Sd|`. -/
theorem dspr_adv_le_hyb_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      (dsprSuccHyb I ρ cap n x ph2 - dsprSPHyb I ρ cap n x ph2) + 2 * seedLoss Sd q₁ := by
  rw [tsub_le_iff_right]
  calc dsprSucc I ρ cap n x ph2 ≤ dsprSuccHyb I ρ cap n x ph2 + seedLoss Sd q₁ :=
        twoPhaseExp_le_hyb_add hx h2
    _ ≤ ((dsprSuccHyb I ρ cap n x ph2 - dsprSPHyb I ρ cap n x ph2) +
          dsprSPHyb I ρ cap n x ph2) + seedLoss Sd q₁ := add_le_add le_tsub_add le_rfl
    _ ≤ ((dsprSuccHyb I ρ cap n x ph2 - dsprSPHyb I ρ cap n x ph2) +
          (dsprSP I ρ cap n x ph2 + seedLoss Sd q₁)) + seedLoss Sd q₁ :=
        add_le_add (add_le_add le_rfl (twoPhaseHyb_le_exp_add hx h2)) le_rfl
    _ = (dsprSuccHyb I ρ cap n x ph2 - dsprSPHyb I ρ cap n x ph2) + 2 * seedLoss Sd q₁ +
          dsprSP I ρ cap n x ph2 := by ring

end DSPR

end Exp

end PQ.QROM

#print axioms PQ.QROM.seed_hiding'
#print axioms PQ.QROM.udExact_real_le_ideal_add_of_hyb
#print axioms PQ.QROM.udExact_ideal_le_real_add_of_hyb
#print axioms PQ.QROM.dspr_adv_le_hyb_add
