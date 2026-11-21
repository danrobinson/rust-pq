import PQ.QROM.ExactUd
import PQ.QROM.UdGiven

/-!
# The exact SM-DT-UD game in the QROM: the hybrid worlds are close

`PQ/QROM/ExactUd.lean` reduces the exact two-phase SM-DT-UD game to its hybrid worlds
(`udRealHyb`, `udIdealHyb`: phase 1 decoupled from the row of the hash at the seed) and takes
their closeness as a hypothesis.  This file proves it:

* `udRealHyb_le_idealHyb_add`, `udIdealHyb_le_realHyb_add`: the hybrid worlds are
  `4 q₂ / √|Msg|`-close.
* `ud_exact_real_le_ideal_add`, `ud_exact_ideal_le_real_add`: unconditionally,
  `|Pr[real] − Pr[ideal]| ≤ 4 q₂ / √|Msg| + 2 · seedLoss Sd q₁`
  (`seedLoss Sd q₁ = 4 q₁ / √|Sd|`).

Proof: decompose the hybrid experiments over the leaves `p` of phase 1 (`hybProb_eq_tsum`).  For
a fixed leaf, the post-state of phase 1 depends on the row `R` and on the challenge answers only
through what the leaf has seen (`udSeen`): the target values of its target tweaks and the row at
its collection queries, which lie in rows of non-target tweaks.  Phase 2 is then a `q₂`-query
algorithm against the row, and `ud_embedded_both` (`PQ/QROM/UdGiven.lean`) bounds the difference
of the two worlds by `4 q₂ / √|Msg|` times the weight of the leaf; the weights add up to at most
one.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Sd Tw Msg Y : Type}

theorem avg_le_avg_add {T : Type} [Fintype T] {f g : T → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ t, f t ≤ g t + c) : avg f ≤ avg g + c :=
  (avg_mono h).trans (avg_add_const_le _ _)

section

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {cap n q₁ q₂ : ℕ}
  {x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) (Tw ⊕ (Tw × Msg)) (Option Y) Out n A}
  {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Bool) u}

/-- What the leaf with histories `t` has seen: the target values of its target tweaks and the
values of the row at its collection queries. -/
def udSeen (t : PreState Tw Msg) (yv : Tw → Option Y) (R : Tw × Msg → Y) :
    (Tw → Y) × (Tw × Msg → Y) :=
  (fun tw ↦ if tw ∈ t.chal then (yv tw).getD 0 else 0, fun tm ↦ if tm ∈ t.coll then R tm else 0)

theorem postOf_real_eq_udSeen (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) (xs : Tw → Msg)
    (p : Σ u, Out u × PreState Tw Msg) :
    postOf I ρ (preCh cap xs) preInit n x F R p =
      prePost I ρ cap n x F p
        (udSeen p.2.2 (tvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) R xs) R) :=
  postOf_eq_preSeen F R xs p

theorem postOf_ideal_eq_udSeen (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) (ys : Tw → Y)
    (p : Σ u, Out u × PreState Tw Msg) :
    postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p =
      prePost I ρ cap n x F p
        (udSeen p.2.2 (yvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) ys) R) := by
  obtain ⟨u, o, t⟩ := p
  unfold postOf prePost
  exact DFunLike.congr_fun (flat_branch_congr (twoRuntime fun _ ↦ F) I
    (preChT cap ys R)
    (preChT cap _ _) PreState.Ext (fun _ ↦ ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun req s t ↦ preChT_ext cap _ _ req s t) (fun req s t ↦ preChT_ext cap _ _ req s t) t
    (preChT_loc cap _ _ _ _ t (fun tw htw ↦ by simp [udSeen, yvals, htw])
      (fun tm htm ↦ by simp [udSeen, htm])) n preInit x u o) (joint ρ)

theorem avg_avg_eq_sum {T : Type} [Fintype T] (f : (Tw × Msg → Y) → T → ℝ≥0∞) :
    (avg fun t : T ↦ avg fun R : Tw × Msg → Y ↦ f R t) =
      ∑ R : Tw × Msg → Y, ∑ t : T,
        ((Fintype.card (Tw × Msg → Y) : ℝ≥0∞)⁻¹ * (Fintype.card T : ℝ≥0∞)⁻¹) * f R t := by
  unfold avg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun t _ ↦ by
    rw [← mul_assoc, mul_comm (Fintype.card T : ℝ≥0∞)⁻¹]

/-- **One leaf of phase 1**: the two worlds are `4 q₂ / √|Msg|`-close up to the weight of the
leaf, in both directions. -/
theorem ud_leaf_both [Nonempty Tw] [Nonempty Msg]
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × PreState Tw Msg) :
    ((avg fun xs : Tw → Msg ↦ avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ (preCh cap xs) preInit n x F R p) (fun l ↦ udWin R l.2 p.2.2)) ≤
      (avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p)
          (fun l ↦ udWin R l.2 p.2.2)) +
        4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) *
          avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
            ENNReal.ofReal (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p).trace.re) ∧
    ((avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p)
          (fun l ↦ udWin R l.2 p.2.2)) ≤
      (avg fun xs : Tw → Msg ↦ avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ (preCh cap xs) preInit n x F R p) (fun l ↦ udWin R l.2 p.2.2)) +
        4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) *
          avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
            ENNReal.ofReal (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p).trace.re) := by
  have hτ : ∀ ya, (prePost I ρ cap n x F p ya).PosSemidef := fun ya ↦
    ((twoRuntime fun _ ↦ F).run I
      (phase1 (preChT cap ya.1 ya.2) preInit n x)).posSemidef_branch_apply p (joint_posSemidef ρ)
  let M : (Tw → Y) × (Tw × Msg → Y) → HybridModel (Dom Sd Tw Msg) Y Bool q₂ := fun ya ↦
    HybridModel.ofSecondPort I F (ph2 P p.1 p.2.1) (prePost I ρ cap n x F p ya) (hτ ya) q₂
      (h2 P p.1 p.2.1) Sigma.snd
  have : Nonempty (Dom Sd Tw Msg) := ⟨(P, (Classical.arbitrary Tw, Classical.arbitrary Msg))⟩
  have h := ud_embedded_both (rowEmb P) F (fun tw ↦ decide (tw ∈ p.2.2.chal)) (udSeen p.2.2)
    (fun k hk yv R v ↦ by
      have hk' : k.1 ∈ p.2.2.chal := by simpa using hk
      unfold udSeen
      refine Prod.ext rfl ?_
      funext tm
      simp only
      split_ifs with hm
      · exact Function.update_of_ne (fun heq ↦ p.2.2.disj tm hm (by rw [heq]; exact hk')) _ _
      · rfl)
    M (fun _ b ↦ b = true) (fun ya ↦ ENNReal.ofReal (prePost I ρ cap n x F p ya).trace.re)
    (fun _ ↦ ENNReal.ofReal_ne_top)
  have hreal : ∀ (R : Tw × Msg → Y) (xs : Tw → Msg),
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ (preCh cap xs) preInit n x F R p) (fun l ↦ udWin R l.2 p.2.2) =
      ENNReal.ofReal (prePost I ρ cap n x F p
          (udSeen p.2.2 (tvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) R xs) R)).trace.re *
        (M (udSeen p.2.2 (tvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) R xs) R)).prob
          (patch F (rowEmb P) R) (fun b ↦ b = true) := by
    intro R xs
    rw [HybridModel.ofSecondPort_prob, postOf_real_eq_udSeen, ← patchRow_eq_patch]
    simp only [udWin]
  have hideal : ∀ (R : Tw × Msg → Y) (ys : Tw → Y),
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p)
        (fun l ↦ udWin R l.2 p.2.2) =
      ENNReal.ofReal (prePost I ρ cap n x F p
          (udSeen p.2.2 (yvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) ys) R)).trace.re *
        (M (udSeen p.2.2 (yvals (fun tw ↦ decide (tw ∈ p.2.2.chal)) ys) R)).prob
          (patch F (rowEmb P) R) (fun b ↦ b = true) := by
    intro R ys
    rw [HybridModel.ofSecondPort_prob, postOf_ideal_eq_udSeen, ← patchRow_eq_patch]
    simp only [udWin]
  have hR : (avg fun xs : Tw → Msg ↦ avg fun R : Tw × Msg → Y ↦
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ (preCh cap xs) preInit n x F R p) (fun l ↦ udWin R l.2 p.2.2)) =
      udEmbReal (rowEmb P) F (fun tw ↦ decide (tw ∈ p.2.2.chal)) (udSeen p.2.2) M
        (fun _ b ↦ b = true) (fun ya ↦ ENNReal.ofReal (prePost I ρ cap n x F p ya).trace.re) := by
    rw [avg_avg_eq_sum]
    unfold udEmbReal
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun xs _ ↦ by rw [hreal]
  have hI : (avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p)
        (fun l ↦ udWin R l.2 p.2.2)) =
      udEmbIdeal (rowEmb P) F (fun tw ↦ decide (tw ∈ p.2.2.chal)) (udSeen p.2.2) M
        (fun _ b ↦ b = true) (fun ya ↦ ENNReal.ofReal (prePost I ρ cap n x F p ya).trace.re) := by
    rw [avg_avg_eq_sum]
    unfold udEmbIdeal
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun ys _ ↦ by rw [hideal]
  have hWt : (avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
      ENNReal.ofReal (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p).trace.re) =
      udEmbWeight (Msg := Msg) (fun tw ↦ decide (tw ∈ p.2.2.chal)) (udSeen p.2.2)
        (fun ya ↦ ENNReal.ofReal (prePost I ρ cap n x F p ya).trace.re) := by
    rw [avg_avg_eq_sum]
    unfold udEmbWeight
    exact Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun ys _ ↦ by
      rw [postOf_ideal_eq_udSeen]
  rw [hR, hI, hWt]
  exact h

/-- The hybrid experiment with challenger randomness, decomposed over the leaves of phase 1. -/
theorem avg_twoPhaseHyb_eq_tsum {Ω : Type} [Fintype Ω]
    (ch : Ω → (Tw × Msg → Y) → Tw ⊕ (Tw × Msg) → PreState Tw Msg → Option Y × PreState Tw Msg)
    (hx : IAdv.IsQueryBound n x (firstBudget q₁)) :
    (avg fun ω : Ω ↦ twoPhaseHyb I ρ (ch ω) preInit n x ph2 udWin) =
      avg fun P : Sd ↦ avg fun F : Dom Sd Tw Msg → Y ↦
        ∑' p : Σ u, Out u × PreState Tw Msg, avg fun ω : Ω ↦ avg fun R : Tw × Msg → Y ↦
          leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
            (postOf I ρ (ch ω) preInit n x F R p) (fun l ↦ udWin R l.2 p.2.2) := by
  unfold twoPhaseHyb
  rw [avg_comm]
  refine avg_congr fun P ↦ ?_
  rw [avg_comm]
  refine avg_congr fun F ↦ ?_
  simp only [hybProb_eq_tsum hx, avg_tsum]

theorem tsum_ud_weight_le (F : Dom Sd Tw Msg → Y) :
    ∑' p : Σ u, Out u × PreState Tw Msg, (avg fun ys : Tw → Y ↦ avg fun R : Tw × Msg → Y ↦
      ENNReal.ofReal (postOf I ρ (fun a ↦ preChT cap ys a) preInit n x F R p).trace.re) ≤ 1 := by
  simp only [← avg_tsum]
  refine avg_le fun ys ↦ avg_le fun R ↦ ?_
  exact (tsum_leaf_le (R := twoRuntime fun _ ↦ F) (I := I)
    (phase1 (preChT cap ys R) preInit n x) (joint_posSemidef ρ)).trans (ofReal_trace_joint_le_one ρ)

/-- **SM-DT-UD, hybrid worlds, real ≤ ideal**: `udRealHyb ≤ udIdealHyb + 4 q₂ / √|Msg|`. -/
theorem udRealHyb_le_idealHyb_add [Nonempty Tw] [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udRealHyb I ρ cap n x ph2 ≤ udIdealHyb I ρ cap n x ph2 +
      4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  unfold udRealHyb udIdealHyb
  rw [avg_twoPhaseHyb_eq_tsum (fun xs : Tw → Msg ↦ preCh cap xs) hx,
    avg_twoPhaseHyb_eq_tsum (fun (ys : Tw → Y) a ↦ preChT cap ys a) hx]
  refine avg_le_avg_add fun P ↦ avg_le_avg_add fun F ↦ ?_
  refine (tsum_le_tsum fun p ↦ (ud_leaf_both h2 P F p).1).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_left]
  exact add_le_add le_rfl ((mul_le_mul' le_rfl (tsum_ud_weight_le F)).trans (mul_one _).le)

/-- **SM-DT-UD, hybrid worlds, ideal ≤ real**: `udIdealHyb ≤ udRealHyb + 4 q₂ / √|Msg|`. -/
theorem udIdealHyb_le_realHyb_add [Nonempty Tw] [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udIdealHyb I ρ cap n x ph2 ≤ udRealHyb I ρ cap n x ph2 +
      4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  unfold udRealHyb udIdealHyb
  rw [avg_twoPhaseHyb_eq_tsum (fun xs : Tw → Msg ↦ preCh cap xs) hx,
    avg_twoPhaseHyb_eq_tsum (fun (ys : Tw → Y) a ↦ preChT cap ys a) hx]
  refine avg_le_avg_add fun P ↦ avg_le_avg_add fun F ↦ ?_
  refine (tsum_le_tsum fun p ↦ (ud_leaf_both h2 P F p).2).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_left]
  exact add_le_add le_rfl ((mul_le_mul' le_rfl (tsum_ud_weight_le F)).trans (mul_one _).le)

/-- **SM-DT-UD in the QROM, exact adaptive two-phase game, real ≤ ideal** (unconditional):
`Pr[real outputs 1] ≤ Pr[ideal outputs 1] + 4 q₂ / √|Msg| + 2 · (4 q₁ / √|Sd|)`. -/
theorem ud_exact_real_le_ideal_add [Nonempty Tw] [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udReal I ρ cap n x ph2 ≤ udIdeal I ρ cap n x ph2 +
      (4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) + 2 * seedLoss Sd q₁) :=
  udExact_real_le_ideal_add_of_hyb hx h2 (udRealHyb_le_idealHyb_add hx h2)

/-- **SM-DT-UD in the QROM, exact adaptive two-phase game, ideal ≤ real** (unconditional). -/
theorem ud_exact_ideal_le_real_add [Nonempty Tw] [Nonempty Msg]
    (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    udIdeal I ρ cap n x ph2 ≤ udReal I ρ cap n x ph2 +
      (4 * q₂ * ((Fintype.card Msg : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) + 2 * seedLoss Sd q₁) :=
  udExact_ideal_le_real_add_of_hyb hx h2 (udIdealHyb_le_realHyb_add hx h2)

end

end PQ.QROM

#print axioms PQ.QROM.udRealHyb_le_idealHyb_add
#print axioms PQ.QROM.udIdealHyb_le_realHyb_add
#print axioms PQ.QROM.ud_exact_real_le_ideal_add
#print axioms PQ.QROM.ud_exact_ideal_le_real_add
