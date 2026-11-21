import PQ.QROM.TwoPhaseAdv

/-!
# Two-phase games with a hidden-then-revealed seed, in the QROM

The setting of the exact stateful games of the SLH-DSA reduction (VCVio's `SM_DT_TCR_Experiment`
and its relatives), with the tweakable hash a uniformly random function and the adversary a
quantum query algorithm in both phases.

## Model

* **Hash.** `Th : Sd × (Tw × Msg) → Y` is uniformly random (`Dom Sd Tw Msg := Sd × (Tw × Msg)`):
  one random function keyed by the public seed.  The adversary has *quantum* access to all of
  `Th` (every seed, every tweak, every message) in both phases, through the two-port signature
  `qrom2Spec`: port `false` is the access of phase 1, port `true` the access of phase 2.  In the
  real game both ports are answered with the oracle unitary of `Th` (`twoRuntime fun _ ↦ Th`).
  The two ports only name the phase of a call; they let the proof change the function seen by
  phase 1 without changing the one seen by phase 2.
* **Hidden-then-revealed seed.** `P : Sd` is uniform and independent of `Th`.  Phase 1 does not
  receive `P`: syntactically, the phase-1 adversary `x` does not depend on `P`.  It still may
  query `Th` at every seed, `P` included, in superposition.  Phase 2 receives `P`: the phase-2
  program `ph2 P u o` depends on `P`, on the classical output `o` of phase 1, and continues on
  the quantum register `u` that phase 1 left behind.
* **Classical challenge oracle.** Phase 1 is an interactive adversary `IAdv` (see
  `PQ/QROM/TwoPhaseAdv.lean`): between quantum segments it sends classical requests `Req` to the
  challenger and receives classical responses `Resp`.  The challenger is the deterministic
  function `ch a : Req → St → Resp × St`, where `a := fun tm ↦ Th (P, tm)` is the row of the hash
  at the hidden seed and `St` is the challenger's state, threaded and recorded by the game
  (`IAdv.flat`), never by the adversary.
* **Budgets.** Phase 1 makes at most `q₁` calls of port `false` and none of port `true` on
  every path; phase 2 makes at most `q₂` calls of port `true` and none of port `false`
  (`firstBudget q₁`, `secondBudget q₂`).  The number of classical requests is at most `n`
  (any `n`); it does not enter the bounds.
* **Win.** A predicate `win a r s` of the row `a` of the hash at the seed, the classical output
  `r` of phase 2 and the final challenger state `s`.

`twoPhaseExp` is the exact winning probability: the uniform average over `(P, Th)` of the Born
probability of the winning leaves of the single program `phase 1 >>= phase 2` (`composite`).

## Seed hiding

`seed_hiding`: `√(twoPhaseExp) ≤ √(twoPhaseHyb) + 2 q₁ / √|Sd|`, where in `twoPhaseHyb` phase 1
has quantum access to a uniformly random `F` that is independent of the row `R` of the hash at
the seed; the challenger answers from `R`; phase 2 has quantum access to `F` with the row of
the seed `P` replaced by `R`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

/-! ## Uniform averages -/

section Avg

variable {T T' : Type} [Fintype T] [Fintype T']

/-- The uniform average over a finite type. -/
noncomputable def avg (f : T → ℝ≥0∞) : ℝ≥0∞ := ∑ t, (Fintype.card T : ℝ≥0∞)⁻¹ * f t

theorem avg_mono {f g : T → ℝ≥0∞} (h : ∀ t, f t ≤ g t) : avg f ≤ avg g :=
  Finset.sum_le_sum fun t _ ↦ mul_le_mul' le_rfl (h t)

theorem avg_congr {f g : T → ℝ≥0∞} (h : ∀ t, f t = g t) : avg f = avg g :=
  Finset.sum_congr rfl fun t _ ↦ by rw [h t]

theorem avg_le {f : T → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ t, f t ≤ c) : avg f ≤ c := by
  unfold avg
  rcases isEmpty_or_nonempty T with hT | hT
  · simp
  · calc ∑ t, (Fintype.card T : ℝ≥0∞)⁻¹ * f t ≤ ∑ _t : T, (Fintype.card T : ℝ≥0∞)⁻¹ * c :=
          Finset.sum_le_sum fun t _ ↦ mul_le_mul' le_rfl (h t)
      _ = c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
            ENNReal.mul_inv_cancel (by simp)
              (ENNReal.natCast_ne_top _), one_mul]

theorem avg_mul_left (c : ℝ≥0∞) (f : T → ℝ≥0∞) : avg (fun t ↦ c * f t) = c * avg f := by
  unfold avg
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ ↦ mul_left_comm _ _ _

theorem avg_comm (f : T → T' → ℝ≥0∞) :
    avg (fun a ↦ avg fun b ↦ f a b) = avg fun b ↦ avg fun a ↦ f a b := by
  unfold avg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ mul_left_comm _ _ _

theorem avg_tsum {ι : Type*} (f : T → ι → ℝ≥0∞) :
    avg (fun t ↦ ∑' i, f t i) = ∑' i, avg fun t ↦ f t i := by
  unfold avg
  rw [Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  exact Finset.sum_congr rfl fun t _ ↦ ENNReal.tsum_mul_left.symm

/-- Minkowski for uniform averages, in the square-root domain. -/
theorem sqrt_avg_le (a b c : T → ℝ≥0∞)
    (h : ∀ t, a t ^ (2⁻¹ : ℝ) ≤ b t ^ (2⁻¹ : ℝ) + c t ^ (2⁻¹ : ℝ)) :
    avg a ^ (2⁻¹ : ℝ) ≤ avg b ^ (2⁻¹ : ℝ) + avg c ^ (2⁻¹ : ℝ) :=
  sqrt_sum_le (fun _ ↦ (Fintype.card T : ℝ≥0∞)⁻¹) a b c h

end Avg

/-! ## The seed-keyed domain -/

/-- The domain of the seed-keyed hash: seed, then tweak and message. -/
abbrev Dom (Sd Tw Msg : Type) : Type := Sd × (Tw × Msg)

variable {Sd Tw Msg Y : Type}

/-- The row of the hash at the seed `P`. -/
def rowOf (Th : Dom Sd Tw Msg → Y) (P : Sd) : Tw × Msg → Y := fun tm ↦ Th (P, tm)

/-- `F` with the row of the seed `P` replaced by `R`. -/
def patchRow [DecidableEq Sd] (F : Dom Sd Tw Msg → Y) (P : Sd) (R : Tw × Msg → Y) :
    Dom Sd Tw Msg → Y :=
  fun z ↦ if z.1 = P then R z.2 else F z

section Patch

variable [DecidableEq Sd]

@[simp]
theorem rowOf_patchRow (F : Dom Sd Tw Msg → Y) (P : Sd) (R : Tw × Msg → Y) :
    rowOf (patchRow F P R) P = R := by
  funext tm
  simp [rowOf, patchRow]

theorem patchRow_rowOf (F : Dom Sd Tw Msg → Y) (P : Sd) (R : Tw × Msg → Y) :
    patchRow (patchRow F P R) P (rowOf F P) = F := by
  funext z
  by_cases h : z.1 = P
  · have hz : z = (P, z.2) := Prod.ext h rfl
    simp only [patchRow, h, ite_true, rowOf]
    rw [← hz]
  · simp [patchRow, h]

theorem patchRow_ne {F : Dom Sd Tw Msg → Y} {P : Sd} {R : Tw × Msg → Y} {z : Dom Sd Tw Msg}
    (h : patchRow F P R z ≠ F z) : z.1 = P := by
  by_contra hne
  exact h (by simp [patchRow, hne])

variable [Fintype Sd] [Fintype Tw] [Fintype Msg] [DecidableEq Tw] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]

omit [DecidableEq Y] in
/-- Resampling the row of the seed: a uniform function is a uniform function with the row of
`P` replaced by an independent uniform row. -/
theorem avg_patchRow (P : Sd) (g : (Dom Sd Tw Msg → Y) → ℝ≥0∞) :
    avg g = avg fun F ↦ avg fun R : Tw × Msg → Y ↦ g (patchRow F P R) := by
  let sw : (Dom Sd Tw Msg → Y) × (Tw × Msg → Y) → (Dom Sd Tw Msg → Y) × (Tw × Msg → Y) :=
    fun FR ↦ (patchRow FR.1 P FR.2, rowOf FR.1 P)
  have hsw : Function.Involutive sw := fun FR ↦ by
    simp only [sw]
    rw [patchRow_rowOf, rowOf_patchRow]
  have e : ∑ FR : (Dom Sd Tw Msg → Y) × (Tw × Msg → Y), g (patchRow FR.1 P FR.2) =
      ∑ FR : (Dom Sd Tw Msg → Y) × (Tw × Msg → Y), g FR.1 :=
    Equiv.sum_comp hsw.toPerm fun FR ↦ g FR.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at e
  unfold avg
  simp only [Finset.mul_sum]
  simp only [← mul_assoc, ← Finset.mul_sum]
  simp only at e
  rw [e]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_assoc, ← mul_assoc _ (Fintype.card (Tw × Msg → Y) : ℝ≥0∞),
    ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _),
    one_mul]

end Patch

/-! ## The game -/

section Game

variable [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg} {Req Resp St Res : Type}

/-- The joint operator of a substate of the program register and the (trivial) runtime
register. -/
noncomputable def joint (ρ : SubState A) : Matrix (A × Unit) (A × Unit) ℂ :=
  ρ.matrix ⊗ₖ (SubState.basis ()).matrix

theorem joint_posSemidef (ρ : SubState A) : (joint ρ).PosSemidef :=
  (ρ.prod (SubState.basis ())).posSemidef

theorem ofReal_trace_joint_le_one (ρ : SubState A) :
    ENNReal.ofReal (joint ρ).trace.re ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (ρ.prod (SubState.basis ())).trace_re_le_one

/-- Phase 2 on the output `o` of phase 1 with the revealed seed `P`, recording the final
challenger state `s` next to its result. -/
def phase2K (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u)
    (P : Sd) (u : QReg) (o : Out u) (s : St) :
    QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res × St) u :=
  (ph2 P u o).bind fun _ r ↦ QuantumComp.pure (r, s)

/-- Phase 1 alone against the challenger `ch`, stopping with its output and the challenger
state. -/
def phase1 (ch : Req → St → Resp × St) (s₀ : St) (n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp Out n A) :
    QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun u ↦ Out u × St) A :=
  IAdv.flat ch (IAdv.stop (L := L) (spec := qrom2Spec (Dom Sd Tw Msg) Y)) n s₀ x

/-- The whole run as one program: phase 1 against the challenger `ch`, then phase 2 with the
seed `P`.  Its leaves carry the result of phase 2 and the final challenger state. -/
def composite (ch : Req → St → Resp × St) (s₀ : St) (n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp Out n A)
    (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u)
    (P : Sd) : QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res × St) A :=
  IAdv.flat ch (phase2K ph2 P) n s₀ x

omit [AddCommGroup Y] in
theorem composite_eq_bind (ch : Req → St → Resp × St) (s₀ : St) (n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp Out n A)
    (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u)
    (P : Sd) :
    composite ch s₀ n x ph2 P =
      (phase1 ch s₀ n x).bind fun u os ↦ phase2K ph2 P u os.1 os.2 :=
  IAdv.flat_eq_bind ch (phase2K ph2 P) n s₀ x

omit [AddCommGroup Y] in
theorem phase2K_isQueryBound
    {ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u}
    {b : Bool → ℕ} (h2 : ∀ P u o, (ph2 P u o).IsQueryBound b) (P : Sd) (u : QReg) (o : Out u)
    (s : St) : (phase2K ph2 P u o s).IsQueryBound b := by
  have h := (h2 P u o).bind (b₂ := 0) fun u' (r : Res) ↦
    QuantumComp.isQueryBound_pure (L := L) (spec := qrom2Spec (Dom Sd Tw Msg) Y)
      (X := fun _ ↦ Res × St) (A := u') (r, s) 0
  rw [add_zero] at h
  exact h

/-- The winning event on the leaves of the composite program. -/
def winLeaf (win : Res → St → Prop) (p : Σ _ : QReg, Res × St) : Prop := win p.2.1 p.2.2

variable (I : L.Interp) (ρ : SubState A) (ch : (Tw × Msg → Y) → Req → St → Resp × St) (s₀ : St)
  (n : ℕ) (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp Out n A)
  (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u)
  (win : (Tw × Msg → Y) → Res → St → Prop)

/-- Winning probability of the real game for the seed `P` and the hash `Th`: both phases have
quantum access to `Th`, the challenger answers from the row of `Th` at `P`. -/
noncomputable def realProb (P : Sd) (Th : Dom Sd Tw Msg → Y) : ℝ≥0∞ :=
  leafProb (twoRuntime fun _ ↦ Th) I (composite (ch (rowOf Th P)) s₀ n x ph2 P) (joint ρ)
    (winLeaf (win (rowOf Th P)))

/-- **The exact two-phase experiment in the QROM**: the seed `P` and the hash `Th` are uniform
and independent. -/
noncomputable def twoPhaseExp : ℝ≥0∞ :=
  avg fun P : Sd ↦ avg fun Th : Dom Sd Tw Msg → Y ↦ realProb I ρ ch s₀ n x ph2 win P Th

/-- Winning probability of the hybrid game: phase 1 has quantum access to `F`, the challenger
answers from the row `R`, phase 2 has quantum access to `F` with the row of the seed `P`
replaced by `R`. -/
noncomputable def hybProb (P : Sd) (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) : ℝ≥0∞ :=
  leafProb (twoRuntime (ports F (patchRow F P R))) I (composite (ch R) s₀ n x ph2 P) (joint ρ)
    (winLeaf (win R))

/-- **The hybrid experiment**: `P`, `F` and the row `R` are uniform and independent. -/
noncomputable def twoPhaseHyb : ℝ≥0∞ :=
  avg fun P : Sd ↦ avg fun F : Dom Sd Tw Msg → Y ↦ avg fun R : Tw × Msg → Y ↦
    hybProb I ρ ch s₀ n x ph2 win P F R

/-- Mass of phase 1 (quantum access to `F`, challenger answers from `R`) on the query input
`k`.  It does not depend on the seed. -/
noncomputable def phase1Mass (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) (k : Dom Sd Tw Msg) :
    ℝ≥0∞ :=
  mass2 I (fun _ ↦ F) (phase1 (ch R) s₀ n x) (joint ρ) false k

variable {I ρ ch s₀ n x ph2 win} {q₁ q₂ : ℕ}

theorem sum_phase1Mass_le (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) :
    ∑ k, phase1Mass I ρ ch s₀ n x F R k ≤ q₁ := by
  refine (sum_mass2_le I (fun _ ↦ F) (joint_posSemidef ρ)
    (b := false) (n := q₁) (hx St (ch R) s₀ false)).trans ?_
  exact (mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le

/-- The Kraus weights of the change of port `false` on the row of the seed, for the composite
program run in the hybrid world: at most the masses of phase 1 alone on that row. -/
theorem seed_kraus_le (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd)
    (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) :
    ∑' j, (twoRuntime (ports F (patchRow F P R))).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦
          stepOp2 (ports F (patchRow F P R)) i r - stepOp2 (fun _ ↦ patchRow F P R) i r)
        (composite (ch R) s₀ n x ph2 P) (joint ρ) j ^ (2⁻¹ : ℝ) ≤
      (4 * q₁ * ∑ k ∈ Finset.univ.filter (fun k : Dom Sd Tw Msg ↦ k.1 = P),
        phase1Mass I ρ ch s₀ n x F R k) ^ (2⁻¹ : ℝ) := by
  set Th := patchRow F P R with hTh
  have hσ := joint_posSemidef ρ
  have hp1 : (phase1 (ch R) s₀ n x).IsQueryBound (firstBudget q₁) := hx St (ch R) s₀
  -- the weights of the composite program are those of phase 1
  have hw : ∀ j, (twoRuntime (ports F Th)).queryWeight I
      (QuantumRuntime.krausWeight fun i r ↦
        stepOp2 (ports F Th) i r - stepOp2 (fun _ ↦ Th) i r)
      (composite (ch R) s₀ n x ph2 P) (joint ρ) j =
      (twoRuntime (ports F Th)).queryWeight I
      (QuantumRuntime.krausWeight fun i r ↦
        stepOp2 (ports F Th) i r - stepOp2 (fun _ ↦ Th) i r)
      (phase1 (ch R) s₀ n x) (joint ρ) j := fun j ↦ by
    rw [composite_eq_bind]
    refine queryWeight_bind_of_zero I _ _ _ (fun u os σ j ↦ ?_) _ j
    refine queryWeight_eq_zero_of_unused I _ (phase2K_isQueryBound h2 P u os.1 os.2)
      (fun i hi σ ↦ ?_) σ j
    cases i with
    | false => exact absurd rfl hi
    | true => exact krausWeight_sub_eq_zero (H := fun _ ↦ Th) (G := ports F Th) rfl σ
  simp only [hw]
  refine (tsum_rpow_queryWeight2_le I (fun _ ↦ Th) (ports F Th) hσ hp1).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have e2 : (Finset.univ.filter fun k ↦ (fun _ : Bool ↦ Th) true k ≠ ports F Th true k) = ∅ := by
    simp [ports]
  have hq : ((firstBudget q₁ false + firstBudget q₁ true : ℕ) : ℝ≥0∞) = q₁ := by
    simp [firstBudget]
  rw [e2, Finset.sum_empty, add_zero, hq]
  refine mul_le_mul' le_rfl ?_
  -- the masses of phase 1 do not depend on the function on port `true`
  have hm : ∀ k, mass2 I (ports F Th) (phase1 (ch R) s₀ n x) (joint ρ) false k =
      phase1Mass I ρ ch s₀ n x F R k := fun k ↦ by
    unfold phase1Mass mass2 QuantumRuntime.indexMass QuantumRuntime.indexMassAt
    refine tsum_congr fun j ↦ ?_
    refine queryWeight_congr_of_unused I hp1 (fun i hi ↦ ?_) _ j
    cases i with
    | false => rfl
    | true => exact absurd rfl hi
  simp only [hm]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk ↦ ?_) fun _ _ _ ↦ zero_le
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, patchRow_ne (F := F) (P := P) (R := R) (z := k) hk.2⟩

/-- **Seed hiding, for fixed seed, hash and row.** The masses are those of phase 1 alone on the
inputs of the row of the seed. -/
theorem sqrt_realProb_le (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd)
    (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) :
    realProb I ρ ch s₀ n x ph2 win P (patchRow F P R) ^ (2⁻¹ : ℝ) ≤
      hybProb I ρ ch s₀ n x ph2 win P F R ^ (2⁻¹ : ℝ) +
        (4 * q₁ * ∑ k ∈ Finset.univ.filter (fun k : Dom Sd Tw Msg ↦ k.1 = P),
          phase1Mass I ρ ch s₀ n x F R k) ^ (2⁻¹ : ℝ) := by
  have h1 := twoRuntime_sqrt_le_kraus I (fun _ ↦ patchRow F P R) (ports F (patchRow F P R))
    (composite (ch R) s₀ n x ph2 P) (joint_posSemidef ρ) (winLeaf (win R))
  unfold realProb hybProb
  rw [rowOf_patchRow]
  exact h1.trans (add_le_add le_rfl (seed_kraus_le hx h2 P F R))

/-- Converse direction of `sqrt_realProb_le`, same masses. -/
theorem sqrt_hybProb_le (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) (P : Sd)
    (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) :
    hybProb I ρ ch s₀ n x ph2 win P F R ^ (2⁻¹ : ℝ) ≤
      realProb I ρ ch s₀ n x ph2 win P (patchRow F P R) ^ (2⁻¹ : ℝ) +
        (4 * q₁ * ∑ k ∈ Finset.univ.filter (fun k : Dom Sd Tw Msg ↦ k.1 = P),
          phase1Mass I ρ ch s₀ n x F R k) ^ (2⁻¹ : ℝ) := by
  have h1 := twoRuntime_sqrt_le_kraus' I (fun _ ↦ patchRow F P R) (ports F (patchRow F P R))
    (composite (ch R) s₀ n x ph2 P) (joint_posSemidef ρ) (winLeaf (win R))
  unfold realProb hybProb
  rw [rowOf_patchRow]
  exact h1.trans (add_le_add le_rfl (seed_kraus_le hx h2 P F R))

/-- The averaged mass term of seed hiding. -/
theorem avg_seed_mass_le (hx : IAdv.IsQueryBound n x (firstBudget q₁)) :
    (avg fun P : Sd ↦ avg fun F : Dom Sd Tw Msg → Y ↦ avg fun R : Tw × Msg → Y ↦
      4 * (q₁ : ℝ≥0∞) * ∑ k ∈ Finset.univ.filter (fun k : Dom Sd Tw Msg ↦ k.1 = P),
        phase1Mass I ρ ch s₀ n x F R k) ^ (2⁻¹ : ℝ) ≤
      2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  rw [← sqrt_four_mul]
  refine sqrt_le_sqrt ?_
  rw [avg_comm]
  refine avg_le fun F ↦ ?_
  rw [avg_comm]
  refine avg_le fun R ↦ ?_
  rw [avg_mul_left]
  refine mul_le_mul' le_rfl ?_
  unfold avg
  rw [← Finset.mul_sum, Finset.sum_fiberwise]
  exact mul_le_mul' le_rfl (sum_phase1Mass_le hx F R)

/-- **Seed hiding.** For a two-phase adversary whose first phase makes at most `q₁` quantum
queries and does not receive the seed, the real experiment and the hybrid experiment (phase 1
sees a function independent of the row of the hash at the seed) satisfy
`√(real) ≤ √(hybrid) + 2 q₁ / √|Sd|`, for every challenger and every winning condition. -/
theorem seed_hiding (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseExp I ρ ch s₀ n x ph2 win ^ (2⁻¹ : ℝ) ≤
      twoPhaseHyb I ρ ch s₀ n x ph2 win ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have hreal : twoPhaseExp I ρ ch s₀ n x ph2 win =
      avg fun P : Sd ↦ avg fun F : Dom Sd Tw Msg → Y ↦ avg fun R : Tw × Msg → Y ↦
        realProb I ρ ch s₀ n x ph2 win P (patchRow F P R) :=
    avg_congr fun P ↦ avg_patchRow P _
  rw [hreal]
  exact (sqrt_avg_le _ _ _ fun P ↦ sqrt_avg_le _ _ _ fun F ↦ sqrt_avg_le _ _ _ fun R ↦
    sqrt_realProb_le hx h2 P F R).trans (add_le_add le_rfl (avg_seed_mass_le hx))

/-- **Seed hiding, converse direction**: `√(hybrid) ≤ √(real) + 2 q₁ / √|Sd|`. -/
theorem seed_hiding' (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseHyb I ρ ch s₀ n x ph2 win ^ (2⁻¹ : ℝ) ≤
      twoPhaseExp I ρ ch s₀ n x ph2 win ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) := by
  have hreal : twoPhaseExp I ρ ch s₀ n x ph2 win =
      avg fun P : Sd ↦ avg fun F : Dom Sd Tw Msg → Y ↦ avg fun R : Tw × Msg → Y ↦
        realProb I ρ ch s₀ n x ph2 win P (patchRow F P R) :=
    avg_congr fun P ↦ avg_patchRow P _
  rw [hreal]
  exact (sqrt_avg_le _ _ _ fun P ↦ sqrt_avg_le _ _ _ fun F ↦ sqrt_avg_le _ _ _ fun R ↦
    sqrt_hybProb_le hx h2 P F R).trans (add_le_add le_rfl (avg_seed_mass_le hx))

/-! ## The hybrid game, leaf by leaf -/

omit [AddCommGroup Y] in
/-- Phase 2 followed by recording the challenger state: the winning leaves are those of
phase 2. -/
theorem leafProb_phase2K (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y)) (I : L.Interp)
    (ph2 : Sd → ∀ u, Out u → QuantumComp L (qrom2Spec (Dom Sd Tw Msg) Y) (fun _ ↦ Res) u)
    (P : Sd) (u : QReg) (o : Out u) (s : St) {σ : Matrix (u × R.D) (u × R.D) ℂ}
    (hσ : σ.PosSemidef) (win : Res → St → Prop) :
    leafProb R I (phase2K ph2 P u o s) σ (winLeaf win) =
      leafProb R I (ph2 P u o) σ (fun p ↦ win p.2 s) := by
  unfold phase2K
  rw [leafProb_bind _ _ hσ]
  refine tsum_congr fun p ↦ ?_
  rw [leafProb_pure]
  rfl

/-- The (unnormalised) post-state of the leaf `p` of phase 1, run with quantum access to `F`
and challenger answers from the row `a`. -/
noncomputable def postOf (I : L.Interp) (ρ : SubState A)
    (ch : (Tw × Msg → Y) → Req → St → Resp × St) (s₀ : St) (n : ℕ)
    (x : IAdv L (qrom2Spec (Dom Sd Tw Msg) Y) Req Resp Out n A)
    (F : Dom Sd Tw Msg → Y) (a : Tw × Msg → Y) (p : Σ u, Out u × St) :
    Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
  ((twoRuntime fun _ ↦ F).run I (phase1 (ch a) s₀ n x)).branch p (joint ρ)

theorem postOf_posSemidef (F : Dom Sd Tw Msg → Y) (a : Tw × Msg → Y) (p : Σ u, Out u × St) :
    (postOf I ρ ch s₀ n x F a p).PosSemidef :=
  ((twoRuntime fun _ ↦ F).run I (phase1 (ch a) s₀ n x)).posSemidef_branch_apply p
    (joint_posSemidef ρ)

/-- The hybrid game, decomposed over the leaves of phase 1: phase 2 runs from the post-state of
the leaf, with quantum access to `F` with the row of the seed replaced by `R`. -/
theorem hybProb_eq_tsum (hx : IAdv.IsQueryBound n x (firstBudget q₁)) (P : Sd)
    (F : Dom Sd Tw Msg → Y) (R : Tw × Msg → Y) :
    hybProb I ρ ch s₀ n x ph2 win P F R =
      ∑' p : Σ u, Out u × St,
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ ch s₀ n x F R p) (fun l ↦ win R l.2 p.2.2) := by
  unfold hybProb
  rw [composite_eq_bind, leafProb_bind _ _ (joint_posSemidef ρ)]
  refine tsum_congr fun p ↦ ?_
  have hrun : (twoRuntime (ports F (patchRow F P R))).run I (phase1 (ch R) s₀ n x) =
      (twoRuntime fun _ ↦ F).run I (phase1 (ch R) s₀ n x) :=
    QuantumRuntime.run_congr_of_isQueryBound I (D := QReg.of Unit)
      (σ₁ := SubState.basis ()) (σ₂ := SubState.basis ())
      (s₁ := fun b ↦ (oracleQuery (ports F (patchRow F P R) b)).frame Unit)
      (s₂ := fun _ ↦ (oracleQuery F).frame Unit) (hx _ (ch R) s₀) fun i hi ↦ by
        cases i with
        | false => rfl
        | true => exact absurd rfl hi
  have hpos : (postOf I ρ ch s₀ n x F R p).PosSemidef := postOf_posSemidef F R p
  have h3 : leafProb (twoRuntime (ports F (patchRow F P R))) I
      (phase2K ph2 P p.1 p.2.1 p.2.2) (postOf I ρ ch s₀ n x F R p) (winLeaf (win R)) =
      leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
        (postOf I ρ ch s₀ n x F R p) (fun l ↦ win R l.2 p.2.2) :=
    leafProb_phase2K (twoRuntime (ports F (patchRow F P R))) I ph2 P p.1 p.2.1 p.2.2 hpos (win R)
  rw [hrun]
  exact h3

/-- **From leaves to the hybrid game.** If, for every seed `P`, function `F` and leaf `p` of
phase 1, phase 2 run from the post-state of `p` wins with probability at most `ε` times the
weight of `p`, on average over the row `R`, then the hybrid game is won with probability at
most `ε`. -/
theorem twoPhaseHyb_le_of_leaf {ε : ℝ≥0∞} (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (hleaf : ∀ (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × St),
      (avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ ch s₀ n x F R p) (fun l ↦ win R l.2 p.2.2)) ≤
      ε * avg fun R : Tw × Msg → Y ↦ ENNReal.ofReal (postOf I ρ ch s₀ n x F R p).trace.re) :
    twoPhaseHyb I ρ ch s₀ n x ph2 win ≤ ε := by
  refine avg_le fun P ↦ avg_le fun F ↦ ?_
  simp only [hybProb_eq_tsum hx]
  rw [avg_tsum]
  refine (tsum_le_tsum (hleaf P F)).trans ?_
  rw [ENNReal.tsum_mul_left, ← avg_tsum]
  refine (mul_le_mul' le_rfl (avg_le (c := 1) fun R ↦ ?_)).trans (mul_one _).le
  exact (tsum_leaf_le (R := twoRuntime fun _ ↦ F) (I := I)
    (phase1 (ch R) s₀ n x) (joint_posSemidef ρ)).trans (ofReal_trace_joint_le_one ρ)

/-- **Two-phase games from leaf bounds**: `√Pr[win] ≤ √ε + 2 q₁ / √|Sd|`. -/
theorem twoPhaseExp_sqrt_le_of_leaf {ε : ℝ≥0∞} (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂))
    (hleaf : ∀ (P : Sd) (F : Dom Sd Tw Msg → Y) (p : Σ u, Out u × St),
      (avg fun R : Tw × Msg → Y ↦
        leafProb (twoRuntime (ports F (patchRow F P R))) I (ph2 P p.1 p.2.1)
          (postOf I ρ ch s₀ n x F R p) (fun l ↦ win R l.2 p.2.2)) ≤
      ε * avg fun R : Tw × Msg → Y ↦ ENNReal.ofReal (postOf I ρ ch s₀ n x F R p).trace.re) :
    twoPhaseExp I ρ ch s₀ n x ph2 win ^ (2⁻¹ : ℝ) ≤
      ε ^ (2⁻¹ : ℝ) + 2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) :=
  (seed_hiding hx h2).trans
    (add_le_add (sqrt_le_sqrt (twoPhaseHyb_le_of_leaf hx hleaf)) le_rfl)

/-- The experiment is a probability. -/
theorem twoPhaseExp_le_one : twoPhaseExp I ρ ch s₀ n x ph2 win ≤ 1 :=
  avg_le fun _ ↦ avg_le fun _ ↦
    (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)

/-- The hybrid experiment is a probability. -/
theorem twoPhaseHyb_le_one : twoPhaseHyb I ρ ch s₀ n x ph2 win ≤ 1 :=
  avg_le fun _ ↦ avg_le fun _ ↦ avg_le fun _ ↦
    (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)

/-- **Seed hiding, additive form**: `real ≤ hybrid + 4 q₁ / √|Sd|`. -/
theorem twoPhaseExp_le_hyb_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseExp I ρ ch s₀ n x ph2 win ≤ twoPhaseHyb I ρ ch s₀ n x ph2 win +
      2 * (2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) :=
  le_add_two_mul_of_sqrt_le twoPhaseExp_le_one twoPhaseHyb_le_one (seed_hiding hx h2)

/-- **Seed hiding, additive form, converse**: `hybrid ≤ real + 4 q₁ / √|Sd|`. -/
theorem twoPhaseHyb_le_exp_add (hx : IAdv.IsQueryBound n x (firstBudget q₁))
    (h2 : ∀ P u o, (ph2 P u o).IsQueryBound (secondBudget q₂)) :
    twoPhaseHyb I ρ ch s₀ n x ph2 win ≤ twoPhaseExp I ρ ch s₀ n x ph2 win +
      2 * (2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) :=
  le_add_two_mul_of_sqrt_le twoPhaseHyb_le_one twoPhaseExp_le_one (seed_hiding' hx h2)

end Game

end PQ.QROM
