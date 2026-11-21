import PQ.QROM.ExactTcr
import PQ.QROM.ExactFv
import PQ.QROM.ExactGenColl
import PQ.QROM.ExactPre
import PQ.QROM.ExactGenPre
import PQ.QROM.ExactUdClosed
import PQ.QROM.ExactDsprClosed
import PQ.QROM.ExactUdTight

/-!
# Exact two-phase games with a first phase making no quantum queries (`q₁ = 0`)

In the composition with the reduction the first phases are classical machines that do no
hashing, so they make zero quantum queries.  For `IAdv.IsQueryBound n x (firstBudget 0)` every
seed-hiding term `q₁ / √|Sd|` of the exact two-phase bounds vanishes.  These are the named
corollaries (trivial algebra from the general theorems):

* `tcr_exact_le_zeroPre`, `tcr_fv_exact_le_zeroPre`, `gen_coll_tcr_exact_le_zeroPre`:
  `Pr[win] ≤ (2 q₂ + 1)² / |Y|`;
* `pre_exact_le_zeroPre`, `gen_pre_exact_le_zeroPre`, `gen_pre_sub_exact_le_zeroPre`:
  `Pr[win] ≤ (2 q₂ + 1)² (1/|Y| + 1/|M|)`;
* `ud_exact_real_le_ideal_add_zeroPre`, `ud_exact_ideal_le_real_add_zeroPre` (one-way-to-hiding
  form, `4 q₂ / √|Msg|`) and `ud_exact_tight_zeroPre` (tight form, `(16 q₂² + 2 n) / |Msg|`);
* `dspr_exact_adv_le_zeroPre`: `Success − SPprob ≤ max 0 (2γ − 1) + 8 q₂ / √|Y|`, and
  `dspr_exact_adv_le_zeroPre_of_card_lt`: `≤ 8 q₂ / √|Y|` for `|Y| < |Msg|`.
-/

open MeasureTheory ENNReal Quantum Matrix

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

theorem zeroPre_sq (a c : ℝ≥0∞) : (a ^ (2⁻¹ : ℝ) + 2 * ((0 : ℕ) : ℝ≥0∞) * c) ^ 2 = a := by
  rw [Nat.cast_zero, mul_zero, zero_mul, add_zero, sq_sqrt]

theorem seedLoss_zero (Sd : Type) [Fintype Sd] : seedLoss Sd 0 = 0 := by
  simp [seedLoss]

variable {Sd Tw Msg Y : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg} {I : L.Interp} {ρ : SubState A}
  {cap n q₂ : ℕ}

/-- **SM-DT-TCR, classical first phase**: `Pr[win] ≤ (2 q₂ + 1)² / |Y|`. -/
theorem tcr_exact_le_zeroPre [Inhabited Tw]
    {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) (Option Y) Out n A}
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    tcrExp I ρ cap n x ph2 ≤ (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  (tcr_exact_le hx h2).trans (zeroPre_sq _ _).le

/-- **SM-DT-TCR, source final validity, classical first phase**. -/
theorem tcr_fv_exact_le_zeroPre [Inhabited Tw]
    {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A}
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    tcrFvExp I ρ cap n x ph2 ≤ (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  (tcr_fv_exact_le hx h2).trans (zeroPre_sq _ _).le

/-- **SM-DT-TCR with a general collection, classical first phase**. -/
theorem gen_coll_tcr_exact_le_zeroPre {ι : Type} {MsgC : ι → Type} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (MsgC i)] [∀ i, DecidableEq (MsgC i)] [Inhabited Tw]
    {x : IAdv L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y)
      ((Tw × Msg) ⊕ (Tw × (Σ i, MsgC i))) (Option Y) Out n A}
    {ph2 : Sd → ∀ u, Out u →
      QuantumComp L (qrom2Spec (Dom Sd Tw (Msg ⊕ (Σ i, MsgC i))) Y) (fun _ ↦ ℕ × Msg) u}
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genCollTcrExp I ρ cap n x ph2 ≤ (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  (gen_coll_tcr_exact_le hx h2).trans (zeroPre_sq _ _).le

/-- **SM-DT-PRE, classical first phase**: `Pr[win] ≤ (2 q₂ + 1)² (1/|Y| + 1/|Msg|)`. -/
theorem pre_exact_le_zeroPre [Inhabited Tw]
    {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    preExp I ρ cap n x ph2 ≤ (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Msg : ℝ≥0∞)⁻¹) :=
  (pre_exact_le hx h2).trans (zeroPre_sq _ _).le

/-- **SM-DT-PRE with planted inputs in `Mp`, classical first phase**. -/
theorem gen_pre_exact_le_zeroPre {Mp : Type} [Fintype Mp] [DecidableEq Mp] [Inhabited Tw]
    {emb : Mp ↪ Msg}
    {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Msg) u}
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    genPreExp I ρ cap n emb x ph2 ≤ (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹) :=
  (gen_pre_exact_le hx h2).trans (zeroPre_sq _ _).le

/-- **SM-DT-PRE with the adversary's preimage in `Mp`, classical first phase**. -/
theorem gen_pre_sub_exact_le_zeroPre {Mp : Type} [Fintype Mp] [DecidableEq Mp] [Inhabited Tw]
    {emb : Mp ↪ Msg}
    {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
    {ph2' : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Mp) u}
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2' P u o).IsQueryBound (secondBudget q₂)) :
    genPreSubExp I ρ cap n emb x ph2' ≤ (2 * (q₂ : ℝ≥0∞) + 1) ^ 2 *
      ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card Mp : ℝ≥0∞)⁻¹) :=
  (gen_pre_sub_exact_le hx h2).trans (zeroPre_sq _ _).le

section UD

variable {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Bool) u}

/-- **SM-DT-UD, classical first phase, one-way-to-hiding form, real ≤ ideal**. -/
theorem ud_exact_real_le_ideal_add_zeroPre [Nonempty Tw] [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udReal I ρ cap n x ph2 ≤ udIdeal I ρ cap n x ph2 +
      4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := ud_exact_real_le_ideal_add (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [seedLoss_zero, mul_zero, add_zero] at h

/-- **SM-DT-UD, classical first phase, one-way-to-hiding form, ideal ≤ real**. -/
theorem ud_exact_ideal_le_real_add_zeroPre [Nonempty Tw] [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udIdeal I ρ cap n x ph2 ≤ udReal I ρ cap n x ph2 +
      4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := ud_exact_ideal_le_real_add (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [seedLoss_zero, mul_zero, add_zero] at h

/-- **SM-DT-UD, classical first phase, tight form**:
`|Pr[real] − Pr[ideal]| ≤ (16 q₂² + 2 n) / |Msg|`. -/
theorem ud_exact_tight_zeroPre [Nonempty Msg] (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    |(udReal I ρ cap n x ph2).toReal - (udIdeal I ρ cap n x ph2).toReal| ≤
      (16 * (q₂ : ℝ) ^ 2 + 2 * n) / Fintype.card Msg := by
  have h := ud_exact_tight (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [zero_add] at h

end UD

section DSPR

variable {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) ((Tw × Msg) ⊕ (Tw × Msg)) Y Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ ℕ × Bool) u}

/-- **SM-DT-DSPR (source final validity), classical first phase**:
`Success − SPprob ≤ max 0 (2γ − 1) + 8 q₂ / √|Y|`. -/
theorem dspr_exact_adv_le_zeroPre [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      dsprTrivial Msg Y + 8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := dspr_exact_adv_le (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [seedLoss_zero, mul_zero, add_zero] at h

/-- For a compressing hash the trivial term vanishes: `Success − SPprob ≤ 8 q₂ / √|Y|`. -/
theorem dspr_exact_adv_le_zeroPre_of_card_lt [Inhabited Tw] [Nonempty Msg] [Nontrivial Y]
    (hcard : Fintype.card Y < Fintype.card Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget 0))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    dsprSucc I ρ cap n x ph2 - dsprSP I ρ cap n x ph2 ≤
      8 * q₂ * ((Fintype.card Y : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have h := dspr_exact_adv_le_zeroPre (I := I) (ρ := ρ) (cap := cap) hx h2
  rwa [dsprTrivial_eq_zero hcard, zero_add] at h

end DSPR

end PQ.QROM

#print axioms PQ.QROM.tcr_exact_le_zeroPre
#print axioms PQ.QROM.tcr_fv_exact_le_zeroPre
#print axioms PQ.QROM.gen_coll_tcr_exact_le_zeroPre
#print axioms PQ.QROM.pre_exact_le_zeroPre
#print axioms PQ.QROM.gen_pre_exact_le_zeroPre
#print axioms PQ.QROM.gen_pre_sub_exact_le_zeroPre
#print axioms PQ.QROM.ud_exact_real_le_ideal_add_zeroPre
#print axioms PQ.QROM.ud_exact_ideal_le_real_add_zeroPre
#print axioms PQ.QROM.ud_exact_tight_zeroPre
#print axioms PQ.QROM.dspr_exact_adv_le_zeroPre
#print axioms PQ.QROM.dspr_exact_adv_le_zeroPre_of_card_lt
